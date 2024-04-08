/* The header <ctype.h> declares several functions for classifying 
 * and mappings.
 */

#ifndef _CTYPE_
#define _CTYPE_

/* Needed from locale.h: */
#include <locale.h>

/* Functions */
//is functions: 
int   isalnum(int);
int   isalnum_l(int, locale_t);
int   isalpha(int);
int   isalpha_l(int, locale_t);
int   isascii(int);
int   isblank(int);
int   isblank_l(int, locale_t);
int   iscntrl(int);
int   iscntrl_l(int, locale_t);
int   isdigit(int);
int   isdigit_l(int, locale_t);
int   isgraph(int);
int   isgraph_l(int, locale_t);
int   islower(int);
int   islower_l(int, locale_t);
int   isprint(int);
int   isprint_l(int, locale_t);
int   ispunct(int);
int   ispunct_l(int, locale_t);
int   isspace(int);
int   isspace_l(int, locale_t);
int   isupper(int);
int   isupper_l(int, locale_t);
int   isxdigit(int);
int   isxdigit_l(int, locale_t);
int   toascii(int);

//to functions:
int	  toascii(int);
int   tolower(int);
int   tolower_l(int, locale_t);
int   toupper(int);
int   toupper_l(int, locale_t);

#endif
