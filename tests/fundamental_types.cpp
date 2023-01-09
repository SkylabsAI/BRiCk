// floating point
float f;
double d;
long double ld;


void dfun(float, double, long double);

// integral
char c;
signed char sc;
unsigned char uc;
short s;
signed short ss;
unsigned short us;
int i;
signed int si;
unsigned int ui;
long l;
signed long sl;
unsigned long ul;
long long ll;
signed long long sll;
unsigned long long ull;
__int128_t i128;
__uint128_t u128;

void ifun(char,signed char, unsigned char, short, unsigned short, int, unsigned int, long, unsigned long, long long, unsigned long long, __int128_t, __uint128_t);

// character
wchar_t wc;
#if 202002L <= __cplusplus
char8_t c8;
char16_t c16;
char32_t c32;
void cfun(wchar_t, char8_t, char16_t, char32_t);
#elif 201102L <= __cplusplus
char16_t c16;
char32_t c32;
void cfun(wchar_t, char16_t, char32_t);
#else
void cfun(wchar_t);
#endif

// boolean
bool b;
