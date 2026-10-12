#include <stdio.h>
#include <stdlib.h>
typedef unsigned long long u;
u s_pk(u p,int k){ // number of squares mod p^k, known formula via brute small? use recursion
  // count squares mod p^k: formula
  u pk=1; for(int i=0;i<k;i++) pk*=p;
  if(p==2){ if(k==1) return 2; if(k==2) return 2; if(k%2==0) return (pk/6 + 4 + (pk>8?0:0)) ; }
  return 0;
}
int main(int c,char**v){u N=atoll(v[1]);
 // sieve smallest prime factor
 unsigned *spf=calloc(N+1,4);
 for(u i=2;i<=N;i++) if(!spf[i]) for(u j=i;j<=N;j+=i) if(!spf[j]) spf[j]=i;
 for(u n=2;n<=N;n++){
   u m=n; u a=1; int bad=0;
   while(m>1){u p=spf[m];int k=0;u pk=1;while(m%p==0){m/=p;k++;pk*=p;}
     u s;
     if(p==2){ // squares mod 2^k: k=1:2,k=2:2, else floor(2^k/6)+ (k odd?4:3)... use brute for exactness via formula below
       if(k==1)s=2; else if(k==2)s=2; else if(k%2) s=(pk+10)/6; else s=(pk+8)/6; }
     else { if(k%2) s=(pk*p+2*p+1)/(2*(p+1)); else s=(pk*p+p+2)/(2*(p+1)); }
     a*=s;}
   __int128 d=(__int128)a*(a-1); __int128 nn=(__int128)n*n-1;
   int lhs = (a>1) && (nn % d==0);
   int pr = (spf[n]==n && n!=2);
   if(lhs!=pr) printf("mismatch %llu a=%llu\n",n,a);
 }
 return 0;}
