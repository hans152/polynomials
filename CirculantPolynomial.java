/**
 * 
 * @author Andreas Rosowski
 *
 */
public class CirculantPolynomial {
	private static final long P = 2147483647L;
	private static final long[] ONE = {1L, 0L};
	private long[][] ROOTS;
	private long[][] INVERSEROOTS;
	
	public long[] mult(long[] a, long[] b) {
		int N = a.length + b.length - 1;
		int d = 0;
		while(N > 0) {
			d++;
			N >>= 1;
		}
		N = 1 << d;
		long[] omega = {2L, 1L};
		omega = CirculantPolynomial.power(omega, (CirculantPolynomial.P + 1) >> (d-3));
		computeRoots(omega, N >> 3, d-3);
		long[][] aTmp = new long[N][2];
		long[] tmp = {a[0], 0};
		aTmp[0] = tmp;
		for(int i=1;i<a.length;i++) {
			long[] tmp2 = {a[i], 0};
			aTmp[N-i] = tmp2;
		}
		long[][] bTmp = new long[N][2];
		for(int i=0;i<b.length;i++) {
			long[] tmp2 = {b[i], 0};
			bTmp[i] = tmp2;
		}
		long[][] cTmp = multRec(aTmp, bTmp, 0, N);
		long[] c = new long[a.length + b.length - 1];
		for(int i=0;i<c.length;i++) {
			c[i] = (cTmp[i][0] + CirculantPolynomial.P) % CirculantPolynomial.P;
		}
		return c;
	}
	
	private long[][] multRec(long[][] a, long[][] b, int D, int N) {
		if(N <= 8) {
			return multNaiv(a, b, D, N);
		}
		int newN = N >> 1;
		long[][] a1 = new long[newN][2];
		long[][] a2 = new long[newN][2];
		long[][] b1 = new long[newN][2];
		long[][] b2 = new long[newN][2];
		long[][] M;
		long[][] c;
		long[] sqrt = ROOTS[D << 1];
		
		for(int i=0;i<newN;i++) {
			a2[i] = CirculantPolynomial.multiplication(a[i+newN], sqrt);
			a1[i][0] = (a[i][0] + a2[i][0]) % CirculantPolynomial.P;
			a1[i][1] = (a[i][1] + a2[i][1]) % CirculantPolynomial.P;
			b1[i] = CirculantPolynomial.multiplication(b[i], sqrt);
			b2[i][0] = (b[i+newN][0] + b1[i][0]) % CirculantPolynomial.P;
			b2[i][1] = (b[i+newN][1] + b1[i][1]) % CirculantPolynomial.P;
		}
		M = multRec(a1, b2, D << 1, newN);
		
		c = new long[N][2];
		for(int i=0;i<newN;i++) {
			c[i] = M[i];
			a1[i][0] = (a[i][0] - a2[i][0]) % CirculantPolynomial.P;
			a1[i][1] = (a[i][1] - a2[i][1]) % CirculantPolynomial.P;
			b2[i][0] = (-b[i+newN][0] + b1[i][0]) % CirculantPolynomial.P;
			b2[i][1] = (-b[i+newN][1] + b1[i][1]) % CirculantPolynomial.P;
		}
		M = multRec(a1, b2, (D << 1) + 1, newN);
		
		sqrt = INVERSEROOTS[D << 1];
		for(int i=0;i<newN;i++) {
			c[i][0] += M[i][0];
			c[i][0] <<= 30;
			c[i][0] %= CirculantPolynomial.P;
			c[i][1] += M[i][1];
			c[i][1] <<= 30;
			c[i][1] %= CirculantPolynomial.P;
			c[i+newN][0] = c[i][0] - M[i][0];
			c[i+newN][0] %= CirculantPolynomial.P;
			c[i+newN][1] = c[i][1] - M[i][1];
			c[i+newN][1] %= CirculantPolynomial.P;
			c[i] = CirculantPolynomial.multiplication(c[i], sqrt);
		}
		
		return c;
	}
	
	private long[][] multNaiv(long[][] a, long[][] b, int D, int N) {
		long[][] c = new long[N][2];
		int count = 0;
		long[] sqrt = ROOTS[D];
		for(int i=0;i<N;i++) {
			long[] tmp = null;
			for(int j=0;j<N-count;j++) {
				tmp = CirculantPolynomial.multiplication(a[j], b[j+count]);
				c[i][0] += tmp[0];
				c[i][1] += tmp[1];
			}
			c[i][0] %= CirculantPolynomial.P;
			c[i][1] %= CirculantPolynomial.P;
			tmp[0] = 0L;
			tmp[1] = 0L;
			for(int j=N-count;j<N;j++) {
				long[] tmp2 = CirculantPolynomial.multiplication(a[j], b[j-N+count]);
				tmp[0] += tmp2[0];
				tmp[1] += tmp2[1];
			}
			tmp[0] %= CirculantPolynomial.P;
			tmp[1] %= CirculantPolynomial.P;
			tmp = CirculantPolynomial.multiplication(tmp, sqrt);
			c[i][0] = (c[i][0] + tmp[0]) % CirculantPolynomial.P;
			c[i][1] = (c[i][1] + tmp[1]) % CirculantPolynomial.P;
			count++;
		}
		return c;
	}
	
	private void computeRoots(long[] omega, int N, int d) {
		long[][] tmpRoots = new long[d][2];
		long[] currOmega = omega;
		for(int i=0;i<d;i++) {
			tmpRoots[d-i-1] = currOmega;
			currOmega = CirculantPolynomial.square(currOmega);
		}
		ROOTS = new long[N][2];
		INVERSEROOTS = new long[N][2];
		ROOTS[0] = currOmega;
		INVERSEROOTS[0] = currOmega;
		int countN = 1;
		int countRoots = 0;
		while(countN < N) {
			currOmega = tmpRoots[countRoots];
			for(int i=0;i<countN;i++) {
				ROOTS[countN+i] = CirculantPolynomial.multiplication(ROOTS[i], currOmega);
				INVERSEROOTS[(countN << 1)-1-i] = ROOTS[countN+i];
			}
			countRoots++;
			countN <<= 1;
		}
	}
	
	private static long[] power(long[] a, long n) {
		if(n == 0) {
			return CirculantPolynomial.ONE;
		}
		else if(n == 1) {
			return a;
		}
		int highestBit = 32;
		int toAdd = 16;
		while(toAdd > 0) {
			long tmp = n >> highestBit;
			if(tmp == 0) {
				highestBit -= toAdd;
			}
			else if(tmp == 1) {
				break;
			}
			else {
				highestBit += toAdd;
			}
			toAdd >>= 1;
		}
		highestBit--;
		int checkBit = 1 << highestBit;
		long[] result = new long[2];
		result[0] = a[0];
		result[1] = a[1];
		while(checkBit > 0) {
			result = CirculantPolynomial.square(result);
			if((n & checkBit) == checkBit) {
				result = CirculantPolynomial.multiplication(result, a);
			}
			checkBit >>= 1;
		}
		return result;
	}
	
	private static long[] multiplication(long[] a, long[] b) {
		long tmp1 = (a[0] * b[0]) % CirculantPolynomial.P;
		long tmp2 = (a[1] * b[1]) % CirculantPolynomial.P;
		tmp2 *= 3;
		tmp2 %= CirculantPolynomial.P;
		tmp1 += tmp2;
		tmp1 %= CirculantPolynomial.P;
		long tmp3 = (a[0] * b[1]) % CirculantPolynomial.P;
		long tmp4 = (a[1] * b[0]) % CirculantPolynomial.P;
		tmp3 += tmp4;
		tmp3 %= CirculantPolynomial.P;
		long[] result = {tmp1, tmp3};
		return result;
	}
	
	private static long[] square(long[] a) {
		long tmp1 = (a[0] * a[0]) % CirculantPolynomial.P;
		long tmp2 = (a[1] * a[1]) % CirculantPolynomial.P;
		tmp2 *= 3;
		tmp2 %= CirculantPolynomial.P;
		tmp1 += tmp2;
		tmp1 %= CirculantPolynomial.P;
		long tmp3 = (a[0] * a[1]) % CirculantPolynomial.P;
		tmp3 <<= 1;
		tmp3 %= CirculantPolynomial.P;
		long[] result = {tmp1, tmp3};
		return result;
	}
}
