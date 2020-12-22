#include <NTL/ZZ.h>
#include <NTL/RR.h>
#include <NTL/vec_ZZ.h>
#include <NTL/mat_ZZ.h>
#include <NTL/vec_GF2.h>
#include <NTL/GF2.h>
#include <NTL/mat_GF2.h>
#include <math.h>

void setFactorBase(vec_ZZ& FB, long& len, long B, ZZ N);
void getSquareRoots(mat_ZZ& SR, vec_ZZ FB, long len, ZZ N);
void sieve(short SI[], long FB[], mat_ZZ SR, long len, long M);
void getSmooth(short SI[], vec_ZZ FB, long len, short T, ZZ N, long M);
int trialDivide(long num, vec_ZZ FB, long len, int factorization[][2]);
void solve(mat_GF2 matrix, ZZ N)


// This will fill the factor base array with primes less than B and will change len
// to the length of the array.
void setFactorBase(vec_ZZ& FB, long& len, long B, ZZ N){
  long i=2;
  ZZ P = to_ZZ(2);
  // -1 and 2 are always in the factor base.
  FB[0]= -1;
  FB[1] = 2;

  while(i<len){
    P++;
    P=NextPrime(P);
    if(Jacobi(N, P)==1){
      FB[i]=P;
      i++;
    }
  }
  // We may have overestimated the size of FB1.
  if(i<len){
    FB.SetLength(i);
    len = i;
  }
  // Or we may have underestimated it.
  else{
    while(P<B){
      FB.SetLength(i+1);
      P+=2;
      P=NextPrime(P);
      if(Jacobi(N, P)==1){
	FB[i] = P;
	i++;
      }
    }
  }
  // We will actually have one more spot open for ease in the large prime stuff.
  len = i;
  FB.SetLength(len+1);
  FB[len] = P*P;  
}

// This will fill the array SR with numbers a such that:
// a=x-floor(sqrt(N)), and x^2 = N (mod p) for each p in the factor base
// Both the positive and negative square roots are held.
// Note that we don't include p=-1, since it is a unit and does not
// contribute any bits to the values of Q(x).

void getSquareRoots(mat_ZZ& SR, vec_ZZ FB, long len, ZZ N){
  long i=2;
  ZZ n = SqrRoot(N);
  ZZ srtemp;
  ZZ P;

  SR.SetDims(len, 2);

  SR[1][0] = (1-n)%2;

  while(i<len){
    P=FB[i];
    srtemp = SqrRootMod(N%P, P);
    SR[i][0]= (srtemp - n)%P;
    SR[i][1]= (P-srtemp-n)%P;
    i++;
  }

}

// Let the sieving begin:
void sieve(short SI[], vec_ZZ FB, mat_ZZ SR, long len, long M){
  // The sieving interval is [-[(M-1)/2], [M/2]], so 0 is at position [(M-1)/2].
  long a;
  long i;
  short bits;
  long P;
  // For every relevant prime in the factor base.
  // Note: -1 is a factor of everything in the left half of the sieving interval.

  //For the prime 2, we only traverse the list once 
    
  a = (M-1)/2;
  // Sieve to the right.
  while(a<M){
    SI[a]+=2;
    a+=2;
  } 
  
  a=(M-1)/2 -2;

  // Then sieve to the left.
  while(a>=0){
    SI[a]+=2;
    a-=2;
  }

  // Now we do the rest of the primes.

  for(i=2; i<len; i++){
    P=to_long(FB[i]);
    bits = (short)NumBits(P);
    a = (M-1)/2 + to_long(SR[i][0]);

    // Sieve to the right.
    while(a<M){
      SI[a]+=bits;
      a+=P;
    } 
    a = (M-1)/2 + to_long(SR[i][1]);
    while(a<M){
      SI[a]+=bits;
      a+=P;
    } 
    
    a=(M-1)/2 + to_long(SR[i][0])-P;

    // Then sieve to the left.
    while(a>=0){
      SI[a]+=bits;
      a-=P;
    }

    a=(M-1)/2 + to_long(SR[i][1])-P;

    while(a>=0){
      SI[a]+=bits;
      a-=P;
    }

  }

  //cout<<len<<endl;

  //for(i=0; i<M; i++)
  //  cout<<SI[i]<<" ";

}

// This function will pick out the smooth elements from our sieving interval.
void getSmooth(short SI[], vec_ZZ FB, long len, short T, ZZ N, long M){
  
  // These two arrays will hold the position in which the number of bits 
  // of Q(x) increases and decreases by 1.
  long *leftbits;
  long *rightbits;
  
  // The number of bits of Q(x) at the extreme ends and middle of the intervals.
  short leftmax, min0;
  
  // Q(x) = (x+n)^2 -N;
  ZZ n = SqrRoot(N);
  ZZ two = to_ZZ(2);
  
  // The smooth guys. Stores the x's.
  vec_ZZ sguys;
  vec_ZZ.SetLength(len+10);

  long count=0;
  
  short i;
  long j, k;
  long mid = (M-1)/2;  //The middle of the sieving interval, equivalent to zero.

  // This will hold the factorization of a number in the sieve array if it is smooth.
  int factorization[10][2];
  int smooth=0; // Counts the number of smooth elements.


  mat_GF2 matrix;
  matrix.SetDims(len+10, len);

  // We use 10 more smooth elts than the size of the factor base for 
  // a better than 1/1000 chance of finding a nontrivial factor.
  long num = 0;

  // A flag that will tell us when we're done finding smooth elements.
  int enough = 0;
  int s; // Another flag to determine smoothness.

  // Find the extreme numbers of bits.
  leftmax = NumBits(sqr(to_ZZ(-mid+n))-N);
  min0 = NumBits(sqr(n)-N);
  
  leftbits = new long[leftmax-min0+2];
  rightbits = new long[leftmax-min0+2];
  
  // Find the first element in the sieving interval, going right, 
  // that has a different number of bits.
  // That is, we solve Q(x)=2^m
  leftbits[0]=0;
  rightbits[0]=mid;

  for(i=1; i<=leftmax-min0; i++)
    leftbits[i]=mid+to_long(SqrRoot(-power(two, leftmax-i)+N)-n)+1;

  for(i=1; i<=leftmax-min0; i++)
    rightbits[i]=mid+to_long(SqrRoot(power(two, min0+i-1)+N)-n)+1;

  leftbits[leftmax-min0+1]=mid;
  rightbits[leftmax-min0+1]=M;

  // Now we can begin to test which of the elements are smooth by
  // seeing if the difference between the number of bits of Q(x) and 
  // the number of bits stored in the sieving interval is <= T.

  // First we check the stuff to the left.
  for(i=0; i<leftmax-min0+1 && !enough; i++){
    for(j=leftbits[i] ; j<leftbits[i+1]; j++) {
      if(leftmax-i-SI[j]<=T){
	count++;
	s=trialDivide(to_long(sqr(to_ZZ(j-mid)+n)-N), FB, len, factorization);
	if(s){
	  smooth++;
	  sguys[smooth] = to_ZZ(j-mid);
	  num = factorization[0][0];
	  for(k=0; k<num; k++){
	    matrix[smooth][factorization[k+1][0]] = ((factorization[k+1][1])%2);
	  }
	  //If we have a smooth element, then pop it into the matrix.
	}
	// If we have enough smooth elements, then break out of here and 
	// Let's solve this stinkin' matrix!
	if (smooth == len+10){
	  enough = 1;
	  solve(matrix, sguys, N);
	  break;
	}
      }
    }
  } 

  // Then we check the stuff to the right.
  for(i=0; i<leftmax-min0+1 && !enough; i++){
    for(j=rightbits[i] ; j<rightbits[i+1]; j++) {
      if(min0+i-SI[j]<=T){
	count++;
	s=trialDivide(to_long(sqr(to_ZZ(j-mid)+n)-N), FB, len, factorization);
	if(s){
	  smooth++;
	  sguys[smooth] = to_ZZ(j-mid);
	  num = factorization[0][0];
	  temp = x_coord[smooth-1];
	  for(k=0; k<num; k++){
	    matrix[smooth][factorization[k+1][0]] = ((factorization[k+1][1])%2);
	  }
	  // If we have a smooth element, then pop it into the matrix.
	}
	// If we have enough smooth elements, then break out of here and 
	// Let's solve this stinkin' matrix!
	if (smooth == len+10){
	  enough = 1;
	  solve(matrix, sguys, N);
	  break;
	}
      }
    }
  }
  cout<<smooth<<" smooth elements.\n\n";
}

// Returns true if the number is smooth.

int trialDivide(long num, vec_ZZ FB, long len, int factorization[][2]){
  long i;
  long num2 = num;
  // factorization will hold the factorization of the number num.
  // The first array will hold the position of the prime factors
  // and the second will hold the exponent.
  // This will be the index of the number of factors.
  int factors=1;

  long P;

  // Do the special case of negatives.
  if (num<0){
    factorization[1][0]=0;
    factorization[1][1]=1;
    factors++;
    num=-num;
  }

  // Now do trial division of the number to find out if it is indeed smooth
  // and to find the prime factors.

  for(i=1; i<len; i++){
    P=to_long(FB[i]);
    if(!(num%P)){
      factorization[factors][0]=i;
      factorization[factors][1]=1;
      num/=P;
      
      while(!(num%P)){
	factorization[factors][1]++;
	num/=P;
      }  
      factors++;   
    }
  }

  // The number is smooth if num == 1;
  if(num==1){
    //cout<<num2<<endl;
    factorization[0][0]=factors-1;
    return(1);
  }
  /*
    Here we will deal with the case in which we have a large prime factor
    remaining after sifting through the factor base. In practice, if we have
    the threshold bound T optimized for the basic case, then we add the number
    of bits of (p_max)^2 to T to test for this case.
    
    else if (num < FB[len]){
    factorization[factors][0]=num;
    // We know the bottom will be true, so we probably won't even include it.
    factorization[factors][1]=1;
    factorization[0][0] = factors;
    return(2);
    }

  */
  else
    return(0);
}

// Here's where all the magic comes to its completion

void solve(mat_GF2 m, vec_ZZ sguys, vec_ZZ FB, ZZ N){

  int i,k;
  long j;
  mat_GF2 K;
  ZZ Y= to_ZZ(0);
  ZZ X =to_ZZ(1);
  ZZ n=SqrRoot(N);
  int factorization[][2];
  cout<<"Sieving done. Solving the matrix.\n\n";
  long len= m.NumCols();
  int factorization[10][2];
  int expholder[len];
  ZZ factor;
  int done= 0;
  
  K=kernel(m);

  for(i=0; i<K.NumRows() && (!done); i++){
	for(j=0; j<len; j++){
		if(K[i][j]){
		 Y+=sguys[j];
		 trialDivide(sqr(sguys[j]+n)-N, vec_ZZ FB, len, factorization);
		 for(k=1; k<=factorization[0][0]; k++){
		 	expholder[factorization[k][0]]+=factorization[k][1];
		 }
		}
	}
	// We have finished recording information. Now let's form X.
	for(j=0; j<len; j++){
		X*=power(FB[j], expholder[j]/2);
	}

	factor= GCD((X-Y)%N,N);
	if(ProbPrime(factor)){
		cout<<factor<<", prime factor.";
		if(ProbPrime(N/factor)){
			cout<<(N/factor)<<", prime factor.";
			done = 1;
		}
	}
	else{
		if(ProbPrime(N/factor)){
			cout<<(N/factor)<<", prime factor.";
		}
	}
  }
}

int main(){

  // number to be factored.
  ZZ N = to_ZZ(1475967391);

  // Bound for the size of primes in the factor base.
  long B = to_long(TruncToZZ(pow(exp(pow(log(to_RR(N))*log(log(to_RR(N))), to_RR(.5))), sqrt(to_RR(.125))))) + 30;

  // Length of the Sieving Interval.
  // The sieving interval itself will be [-M/2 + 1, M/2]
  long M = B*B*B;

  // Treshhold for sieving.
  short T;

  // Setting the length of the factor base array based on the prime number theorem.
  long len = to_long(to_RR(B)/to_RR(log(B)))/2;

  // The largest prime in the factor base.
  ZZ p_max;

  // The factor base. An extra spot will hold the square of the
  // largest prime in the factor base.
  vec_ZZ FB;
  FB.SetLength(len);

  // Where we hold the square roots of N mod p.
  mat_ZZ SR;

  // The sieving interval. The way this will work is that each number 
  // in the interval will represent a Q(x), but only the number of bits 
  // are recorded.
  short *SI = new short[M];

  // It is crucial that every element in this array be zero initially;
  for(long i=0; i<M; i++)
    SI[i]=0;

  cout<<"\nBeginning factorization for "<<N<<".\n\n";

  setFactorBase(FB, len, B, N);
  
  cout<<"Factor base complete: "<<len<<" factors.\n\n";

  getSquareRoots(SR, FB, len, N);

  cout<<"Beginning sieving.\n\n";

  //Now we do the sieving.
  sieve(SI, FB, SR, len, M);

  cout<<"Sieving complete: ";

  p_max = FB[len-1];

  // Set the threshold.
  T= (short)to_long(TruncToZZ(log(to_RR(N))/2 + log(to_RR(M)) - 2*log(to_RR(p_max))));
  
  // Now get the smooth elements.
  getSmooth(SI, FB, len, T, N, M);

}
