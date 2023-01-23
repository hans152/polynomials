/**
 * 
 * @author Andreas Rosowski
 *
 */
public class CirculantPolynomial {
	private static final long P = 2147483647L;
	private static final long[] ONE = {1L, 0L};
	private final long[][] cache = new long[4][2];
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
		omega = CirculantPolynomial.power(omega, (CirculantPolynomial.P + 1) >> (d-2));
		computeRoots(omega, N>>2, d-2);
		long[][] aTmp = new long[N][2];
		aTmp[0][0] = a[0];
		aTmp[0][1] = 0L;
		for(int i=1;i<a.length;i++) {
			long[] tmp2 = {a[i], 0};
			aTmp[N-i] = tmp2;
		}
		long[][] bTmp = new long[N][2];
		for(int i=0;i<b.length;i++) {
			long[] tmp2 = {b[i], 0};
			bTmp[i] = tmp2;
		}
		multRecPre(aTmp, bTmp, N, 0, 0);
		long[] c = new long[a.length + b.length - 1];
		for(int i=0;i<c.length;i++) {
			bTmp[i][0] *= (CirculantPolynomial.P + 1) >> (d-2);
			bTmp[i][0] %= CirculantPolynomial.P;
			c[i] = (bTmp[i][0] + CirculantPolynomial.P) % CirculantPolynomial.P;
		}
		return c;
	}
	
	private void multRecPre(long[][] a, long[][] b, int N, int la, int lb) {
		if(N <= 4) {
			multNaiv(a, b, 0, N, la, lb);
			return;
		}
		int newN = N >> 1;
		long[] tmp = new long[2];
		
		for(int i=0;i<newN;i++) {
			tmp[0] = a[la+i+newN][0];
			tmp[1] = a[la+i+newN][1];
			a[la+i+newN][0] += a[la+i][0];
			a[la+i+newN][0] %= CirculantPolynomial.P;
			a[la+i+newN][1] += a[la+i][1];
			a[la+i+newN][1] %= CirculantPolynomial.P;
			a[la+i][0] -= tmp[0];
			a[la+i][0] %= CirculantPolynomial.P;
			a[la+i][1] -= tmp[1];
			a[la+i][1] %= CirculantPolynomial.P;
			tmp[0] = b[lb+i][0];
			tmp[1] = b[lb+i][1];
			b[lb+i][0] += b[lb+i+newN][0];
			b[lb+i][0] %= CirculantPolynomial.P;
			b[lb+i][1] += b[lb+i+newN][1];
			b[lb+i][1] %= CirculantPolynomial.P;
			b[lb+i+newN][0] = (tmp[0] - b[lb+i+newN][0]) % CirculantPolynomial.P;
			b[lb+i+newN][1] = (tmp[1] - b[lb+i+newN][1]) % CirculantPolynomial.P;
		}
		multRecPre(a, b, newN, la+newN, lb);
		multRec(a, b, 1, newN, la, lb+newN);
		
		for(int i=0;i<newN;i++) {
			tmp[0] = b[lb+i][0];
			tmp[1] = b[lb+i][1];
			b[lb+i][0] += b[lb+i+newN][0];
			b[lb+i][1] += b[lb+i+newN][1];
			b[lb+i][0] %= CirculantPolynomial.P;
			b[lb+i][1] %= CirculantPolynomial.P;
			b[lb+i+newN][0] = tmp[0] - b[lb+i+newN][0];
			b[lb+i+newN][1] = tmp[1] - b[lb+i+newN][1];
			b[lb+i+newN][0] %= CirculantPolynomial.P;
			b[lb+i+newN][1] %= CirculantPolynomial.P;
		}
	}
	
	private void multRec(long[][] a, long[][] b, int D, int N, int la, int lb) {
		if(N <= 4) {
			multNaiv(a, b, D, N, la, lb);
			return;
		}
		int newN = N >> 1;
		long[] sqrt = ROOTS[D << 1];
		long[] tmp = new long[2];
		
		for(int i=0;i<newN;i++) {
			a[la+i+newN] = CirculantPolynomial.multiplication(a[la+i+newN], sqrt);
			tmp[0] = a[la+i+newN][0];
			tmp[1] = a[la+i+newN][1];
			a[la+i+newN][0] += a[la+i][0];
			a[la+i+newN][0] %= CirculantPolynomial.P;
			a[la+i+newN][1] += a[la+i][1];
			a[la+i+newN][1] %= CirculantPolynomial.P;
			a[la+i][0] -= tmp[0];
			a[la+i][0] %= CirculantPolynomial.P;
			a[la+i][1] -= tmp[1];
			a[la+i][1] %= CirculantPolynomial.P;
			b[lb+i] = CirculantPolynomial.multiplication(b[lb+i], sqrt);
			tmp[0] = b[lb+i][0];
			tmp[1] = b[lb+i][1];
			b[lb+i][0] += b[lb+i+newN][0];
			b[lb+i][0] %= CirculantPolynomial.P;
			b[lb+i][1] += b[lb+i+newN][1];
			b[lb+i][1] %= CirculantPolynomial.P;
			b[lb+i+newN][0] = (tmp[0] - b[lb+i+newN][0]) % CirculantPolynomial.P;
			b[lb+i+newN][1] = (tmp[1] - b[lb+i+newN][1]) % CirculantPolynomial.P;
		}
		multRec(a, b, D << 1, newN, la+newN, lb);
		multRec(a, b, (D << 1) + 1, newN, la, lb+newN);
		
		sqrt = INVERSEROOTS[D << 1];
		for(int i=0;i<newN;i++) {
			tmp[0] = b[lb+i][0];
			tmp[1] = b[lb+i][1];
			b[lb+i][0] += b[lb+i+newN][0];
			b[lb+i][1] += b[lb+i+newN][1];
			b[lb+i][0] %= CirculantPolynomial.P;
			b[lb+i][1] %= CirculantPolynomial.P;
			b[lb+i+newN][0] = tmp[0] - b[lb+i+newN][0];
			b[lb+i+newN][1] = tmp[1] - b[lb+i+newN][1];
			b[lb+i+newN][0] %= CirculantPolynomial.P;
			b[lb+i+newN][1] %= CirculantPolynomial.P;
			b[lb+i] = CirculantPolynomial.multiplication(b[lb+i], sqrt);
		}
	}
	
	private void multNaiv(long[][] a, long[][] b, int D, int N, int la, int lb) {
		long[][] c = this.cache;
		long[] sqrt = ROOTS[D];
		for(int i=0;i<N;i++) {
			c[i][0] = 0L;
			c[i][1] = 0L;
			long[] tmp = null;
			for(int j=0;j<N-i;j++) {
				tmp = CirculantPolynomial.multiplication(a[la+j], b[lb+j+i]);
				c[i][0] += tmp[0];
				c[i][1] += tmp[1];
			}
			c[i][0] %= CirculantPolynomial.P;
			c[i][1] %= CirculantPolynomial.P;
			tmp[0] = 0L;
			tmp[1] = 0L;
			for(int j=N-i;j<N;j++) {
				long[] tmp2 = CirculantPolynomial.multiplication(a[la+j], b[lb+j-N+i]);
				tmp[0] += tmp2[0];
				tmp[1] += tmp2[1];
			}
			tmp[0] %= CirculantPolynomial.P;
			tmp[1] %= CirculantPolynomial.P;
			tmp = CirculantPolynomial.multiplication(tmp, sqrt);
			c[i][0] = (c[i][0] + tmp[0]) % CirculantPolynomial.P;
			c[i][1] = (c[i][1] + tmp[1]) % CirculantPolynomial.P;
		}
		for(int i=0;i<N;i++) {
			b[lb+i][0] = c[i][0];
			b[lb+i][1] = c[i][1];
		}
	}
	
	private void computeRoots(long[] omega, int N, int d) {
		long[] currOmega = omega;
		if(N == 0) {
			ROOTS = new long[1][2];
			INVERSEROOTS = new long[1][2];
			ROOTS[0] = currOmega;
			INVERSEROOTS[0] = currOmega;
			return;
		}
		long[][] tmpRoots = new long[d][2];
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
		long[] result = a;
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
