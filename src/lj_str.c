/*
** String handling.
** Copyright (C) 2005-2016 Mike Pall. See Copyright Notice in luajit.h
*/

#define lj_str_c
#define LUA_CORE

#include "lj_obj.h"
#include "lj_gc.h"
#include "lj_err.h"
#include "lj_str.h"
#include "lj_char.h"

/* -- String helpers ------------------------------------------------------ */

/* Ordered compare of strings. Assumes string data is 4-byte aligned. */
int32_t LJ_FASTCALL lj_str_cmp(GCstr *a, GCstr *b)
{
  MSize i, n = a->len > b->len ? b->len : a->len;
  for (i = 0; i < n; i += 4) {
    /* Note: innocuous access up to end of string + 3. */
    uint32_t va = *(const uint32_t *)(strdata(a)+i);
    uint32_t vb = *(const uint32_t *)(strdata(b)+i);
    if (va != vb) {
#if LJ_LE
      va = lj_bswap(va); vb = lj_bswap(vb);
#endif
      i -= n;
      if ((int32_t)i >= -3) {
	va >>= 32+(i<<3); vb >>= 32+(i<<3);
	if (va == vb) break;
      }
      return va < vb ? -1 : 1;
    }
  }
  return (int32_t)(a->len - b->len);
}

/* Fast string data comparison. Caveat: unaligned access to 1st string! */
static LJ_AINLINE int str_fastcmp(const char *a, const char *b, MSize len)
{
  MSize i = 0;
  lua_assert(len > 0);
  lua_assert((((uintptr_t)a+len-1) & (LJ_PAGESIZE-1)) <= LJ_PAGESIZE-4);
  do {  /* Note: innocuous access up to end of string + 3. */
    uint32_t v = lj_getu32(a+i) ^ *(const uint32_t *)(b+i);
    if (v) {
      i -= len;
#if LJ_LE
      return (int32_t)i >= -3 ? (v << (32+(i<<3))) : 1;
#else
      return (int32_t)i >= -3 ? (v >> (32+(i<<3))) : 1;
#endif
    }
    i += 4;
  } while (i < len);
  return 0;
}

/* Find fixed string p inside string s. */
const char *lj_str_find(const char *s, const char *p, MSize slen, MSize plen)
{
  if (plen <= slen) {
    if (plen == 0) {
      return s;
    } else {
      int c = *(const uint8_t *)p++;
      plen--; slen -= plen;
      while (slen) {
	const char *q = (const char *)memchr(s, c, slen);
	if (!q) break;
	if (memcmp(q+1, p, plen) == 0) return q;
	q++; slen -= (MSize)(q-s); s = q;
      }
    }
  }
  return NULL;
}

/* Check whether a string has a pattern matching character. */
int lj_str_haspattern(GCstr *s)
{
  const char *p = strdata(s), *q = p + s->len;
  while (p < q) {
    int c = *(const uint8_t *)p++;
    if (lj_char_ispunct(c) && strchr("^$*+?.([%-", c))
      return 1;  /* Found a pattern matching char. */
  }
  return 0;  /* No pattern matching chars found. */
}

/* -- String interning ---------------------------------------------------- */

/* Resize the string hash table (grow and shrink). */
void lj_str_resize(lua_State *L, MSize newmask)
{
  global_State *g = G(L);
  GCRef *newhash;
  MSize i;
  if (g->gc.state == GCSsweepstring || newmask >= LJ_MAX_STRTAB-1)
    return;  /* No resizing during GC traversal or if already too big. */
  newhash = lj_mem_newvec(L, newmask+1, GCRef);
  memset(newhash, 0, (newmask+1)*sizeof(GCRef));
  for (i = g->strmask; i != ~(MSize)0; i--) {  /* Rehash old table. */
    GCobj *p = gcref(g->strhash[i]);
    while (p) {  /* Follow each hash chain and reinsert all strings. */
      MSize h = gco2str(p)->hash & newmask;
      GCobj *next = gcnext(p);
      /* NOBARRIER: The string table is a GC root. */
      setgcrefr(p->gch.nextgc, newhash[h]);
      setgcref(newhash[h], p);
      p = next;
    }
  }
  lj_mem_freevec(g, g->strhash, g->strmask+1, GCRef);
  g->strmask = newmask;
  g->strhash = newhash;
}

#if LUAJIT_SMART_STRINGS
static inline uint32_t
lj_getu24(const uint8_t *v, unsigned len)
{
	uint32_t x = v[0];
	x |= (uint32_t)v[len/2] << 8;
	x |= (uint32_t)v[len-1] << 16;
	return x;
}
#endif

/* Intern a string and return string object. */
GCstr *lj_str_new(lua_State *L, const char *str, size_t lenx)
{
  global_State *g;
  GCstr *s;
  GCobj *o;
  MSize len = (MSize)lenx;
  MSize a, b, h = len;
#if LUAJIT_SMART_STRINGS
  int collisions = 0;
  MSize fh;
#endif
  if (lenx >= LJ_MAX_STR)
    lj_err_msg(L, LJ_ERR_STROV);
  g = G(L);
  /* Compute string hash. Constants taken from lookup3 hash by Bob Jenkins. */
  if (len >= 4) {  /* Caveat: unaligned access! */
    a = lj_getu32(str);
    h ^= lj_getu32(str+len-4);
    b = lj_getu32(str+(len>>1)-2);
    h ^= b; h -= lj_rol(b, 14);
    b += lj_getu32(str+(len>>2)-1);
  } else if (len > 0) {
    a = *(const uint8_t *)str;
    h ^= *(const uint8_t *)(str+len-1);
    b = *(const uint8_t *)(str+(len>>1));
    h ^= b; h -= lj_rol(b, 14);
  } else {
    return &g->strempty;
  }
  a ^= h; a -= lj_rol(h, 11);
  b ^= a; b -= lj_rol(a, 25);
  h ^= b; h -= lj_rol(b, 16);
#if LUAJIT_SMART_STRINGS
  fh = h;
  h &= ~strsmartbit;
#endif
  /* Check if the string has already been interned. */
  o = gcref(g->strhash[h & g->strmask]);
  if (LJ_LIKELY((((uintptr_t)str+len-1) & (LJ_PAGESIZE-1)) <= LJ_PAGESIZE-4)) {
#if LUAJIT_SMART_STRINGS
/* Regular closed-addressing hash table with fill factor 100% has
 * "average maximum" collision chain near 6 (probability of longer
 * collision chain is low).
 * Collision chain of length 40 is certain sign of bad behaviour,
 * so lets react on it.*/
#define max_collisions 40
#define inc_collision_soft() (collisions++)
/* Presence of two equal hashsum should be a signal for bad behaviour */
#define inc_collision_hard() (collisions+=20, 1)
#else
#define inc_collision_hard() (1)
#define inc_collision_soft()
#endif
    while (o != NULL) {
      GCstr *sx = gco2str(o);
      if (sx->hash == h && sx->len == len && inc_collision_hard() &&
                      str_fastcmp(str, strdata(sx), len) == 0) {
	/* Resurrect if dead. Can only happen with fixstring() (keywords). */
	if (isdead(g, o)) flipwhite(o);
	return sx;  /* Return existing string. */
      }
      o = gcnext(o);
      inc_collision_soft();
    }
  } else {  /* Slow path: end of string is too close to a page boundary. */
    while (o != NULL) {
      GCstr *sx = gco2str(o);
      if (sx->hash == h && sx->len == len && inc_collision_hard() &&
                      memcmp(str, strdata(sx), len) == 0) {
	/* Resurrect if dead. Can only happen with fixstring() (keywords). */
	if (isdead(g, o)) flipwhite(o);
	return sx;  /* Return existing string. */
      }
      o = gcnext(o);
      inc_collision_soft();
    }
  }
#if LUAJIT_SMART_STRINGS
  /* "fast" hash function fully consumes all bytes of strings <= 12 bytes */
  if (len > 12) {
    int search_fullh =
       bloomtest(g->strbloom.cur[0], strbloombits0(h)) &&
       bloomtest(g->strbloom.cur[1], strbloombits1(h));
    if (LJ_UNLIKELY(search_fullh || collisions > max_collisions)) {
      const char *v = str;
      MSize l = len;
#if LJ_ARCH_BITS == 64
      uint64_t e=a;
      uint64_t f=b;
      uint64_t c=0xcafedead; /* TODO: xor with randomized seed */
      uint64_t d=0xdeadbeef;
      uint64_t t = fh ^ len;
      if (l < 16) {
	e ^= lj_getu64(v);
	f ^= lj_getu64(v+l-8);
      } else {
	for(; l>16; l-=16, v+=16) {
	  e ^= lj_getu64(v);
	  f ^= lj_getu64(v+8);
	  c += e;
	  d += f;
	  e = lj_rol(e, 5) - d;
	  f = lj_rol(f, 7) - c;
	  c = lj_rol(c, 24) ^ e;
	  d = lj_rol(d, 1) ^ f;
	}
	e ^= lj_getu64(v+l-16);
	f ^= lj_getu64(v+l-8);
      }
      c += f; c -= lj_rol(e,9);
      d += e; d -= lj_rol(f,58);
      t ^= d; t -= lj_rol(d,46);
      c ^= t; c -= lj_rol(t,22);
      d ^= c; d -= lj_rol(c,50);
      t ^= d; t -= lj_rol(d,31);
      c ^= t; c -= lj_rol(t,7);
      d ^= c; d -= lj_rol(c,27);
      t ^= d; t -= lj_rol(d,48);
      fh = (uint32_t)t ^ (uint32_t)(t >> 32);
#else
      MSize c = 0xcafedead; /* TODO: xor with randomized seed */
      MSize d = 0xdeadbeef;
      for(; l>8; l-=8, v+=8) {
	a ^= lj_getu32(v);
	b ^= lj_getu32(v+4);
	c += a;
	d += b;
	a = lj_rol(a, 5) - d;
	b = lj_rol(b, 7) - c;
	c = lj_rol(c, 24) ^ a;
	d = lj_rol(d, 1) ^ b;
      }
      a ^= lj_getu32(v+l-8);
      b ^= lj_getu32(v+l-4);
      c += b; c -= lj_rol(a, 9);
      d += a; d -= lj_rol(b, 18);
      fh ^= len - lj_rol(a^b,7);
      fh += c; fh += lj_rol(d,13);
      d ^= c;  d -= lj_rol(c,25);
      fh ^= d; fh -= lj_rol(d,16);
      c ^= fh; c -= lj_rol(fh,4);
      d ^= c;  d -= lj_rol(c,14);
      fh ^= d; fh -= lj_rol(d,24);
#endif
      fh |= strsmartbit;
      if (search_fullh) {
	/* Recheck if the string has already been interned with "harder" hash. */
	o = gcref(g->strhash[fh & g->strmask]);
	if (LJ_LIKELY((((uintptr_t)str+len-1) & (LJ_PAGESIZE-1)) <= LJ_PAGESIZE-4)) {
	  while (o != NULL) {
	    GCstr *sx = gco2str(o);
	    if (sx->hash == fh && sx->len == len && str_fastcmp(str, strdata(sx), len) == 0) {
	      /* Resurrect if dead. Can only happen with fixstring() (keywords). */
	      if (isdead(g, o)) flipwhite(o);
	      return sx;  /* Return existing string. */
	    }
	    o = gcnext(o);
	  }
	} else {  /* Slow path: end of string is too close to a page boundary. */
	  while (o != NULL) {
	    GCstr *sx = gco2str(o);
	    if (sx->hash == fh && sx->len == len && memcmp(str, strdata(sx), len) == 0) {
	      /* Resurrect if dead. Can only happen with fixstring() (keywords). */
	      if (isdead(g, o)) flipwhite(o);
	      return sx;  /* Return existing string. */
	    }
	    o = gcnext(o);
	  }
	}
      }
      if (collisions > max_collisions) {
	bloomset(g->strbloom.cur[0], strbloombits0(h));
	bloomset(g->strbloom.new[0], strbloombits0(h));
	bloomset(g->strbloom.cur[1], strbloombits1(h));
	bloomset(g->strbloom.new[1], strbloombits1(h));
	h = fh;
      }
    }
  }
#endif
  /* Nope, create a new string. */
  s = lj_mem_newt(L, sizeof(GCstr)+len+1, GCstr);
  newwhite(g, s);
  s->gct = ~LJ_TSTR;
  s->len = len;
  s->hash = h;
  s->reserved = 0;
  memcpy(strdatawr(s), str, len);
  strdatawr(s)[len] = '\0';  /* Zero-terminate string. */
  /* Add it to string hash table. */
  h &= g->strmask;
  s->nextgc = g->strhash[h];
  /* NOBARRIER: The string table is a GC root. */
  setgcref(g->strhash[h], obj2gco(s));
  if (g->strnum++ > g->strmask)  /* Allow a 100% load factor. */
    lj_str_resize(L, (g->strmask<<1)+1);  /* Grow string table. */
  return s;  /* Return newly interned string. */
}

void LJ_FASTCALL lj_str_free(global_State *g, GCstr *s)
{
  g->strnum--;
  lj_mem_free(g, s, sizestring(s));
}

