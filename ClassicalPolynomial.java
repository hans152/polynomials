/**
 * 
 * @author Andreas Rosowski
 *
 */
public class ClassicalPolynomial {
	private static final long P = 2147483647L;
	private static final long[] ONE = {1L, 0L};
	private long[][] ROOTS;
	private long[][][] TMP1;
	private long[][][] TMP2;
	
	public long[] mult(long[] a, long[] b) {
		int N = a.length + b.length - 1;
		int d = 0;
		while(N > 0) {
			d++;
			N >>= 1;
		}
		N = 1 << d;
		TMP1 = new long[d][][];
		TMP2 = new long[d][][];
		long[] omega = {2L, 1L};
		omega = ClassicalPolynomial.power(omega, (ClassicalPolynomial.P + 1) >> d);
		computeRoots(omega, N);
		long[][] aTmp = new long[N][2];
		for(int i=0;i<a.length;i++) {
			long[] tmp = {a[i], 0};
			aTmp[i] = tmp;
		}
		long[][] bTmp = new long[N][2];
		for(int i=0;i<b.length;i++) {
			long[] tmp = {b[i], 0};
			bTmp[i] = tmp;
		}
		aTmp = FFT(aTmp, 1, N, 1, 0, 0, true);
		bTmp = FFT(bTmp, 1, N, 1, 0, 0, false);
		long[][] cTmp = new long[N][2];
		for(int i=0;i<N;i++) {
			cTmp[i] = ClassicalPolynomial.multiplication(aTmp[i], bTmp[i]);
		}
		omega = ClassicalPolynomial.power(omega, N-1);
		cTmp = FFTinverse(cTmp, -1, N, 1, 0, 0, true);
		long[] c = new long[a.length + b.length - 1];
		for(int i=0;i<c.length;i++) {
			cTmp[i][0] *= (ClassicalPolynomial.P + 1) >> d;
			cTmp[i][0] %= ClassicalPolynomial.P;
			c[i] = (cTmp[i][0] + ClassicalPolynomial.P) % ClassicalPolynomial.P;
		}
		return c;
	}
	
	private long[][] FFT(long[][] a, int D, int N, int length, int offset, int depth, boolean isFirst) {
		if(N <= 2) {
			return DFTN2(a, length, offset, depth, isFirst);
		}
		int newN = N >> 1;
		int newD = D << 1;
		long[][] a0 = FFT(a, newD, newN, length << 1, offset, depth+1, true);
		long[][] a1 = FFT(a, newD, newN, length << 1, offset+length, depth+1, false);
		long[][] c;
		if(isFirst) {
			if(TMP1[depth] == null) {
				TMP1[depth] = new long[N][2];
			}
			c = TMP1[depth];
		}
		else {
			if(TMP2[depth] == null) {
				TMP2[depth] = new long[N][2];
			}
			c = TMP2[depth];
		}
		c[0][0] = (a0[0][0] + a1[0][0]) % ClassicalPolynomial.P;
		c[0][1] = (a0[0][1] + a1[0][1]) % ClassicalPolynomial.P;
		c[newN][0] = (a0[0][0] - a1[0][0]) % ClassicalPolynomial.P;
		c[newN][1] = (a0[0][1] - a1[0][1]) % ClassicalPolynomial.P;
		int currD = D;
		long[] currOmega = ROOTS[currD];
		for(int i=1;i<newN;i++) {
			long[] tmp = ClassicalPolynomial.multiplication(a1[i], currOmega);
			c[i][0] = (tmp[0] + a0[i][0]) % ClassicalPolynomial.P;
			c[i][1] = (tmp[1] + a0[i][1]) % ClassicalPolynomial.P;
			c[i+newN][0] = (a0[i][0] - tmp[0]) % ClassicalPolynomial.P;
			c[i+newN][1] = (a0[i][1] - tmp[1]) % ClassicalPolynomial.P;
			currD += D;
			currOmega = ROOTS[currD];
		}
		return c;
	}
	
	private long[][] FFTinverse(long[][] a, int D, int N, int length, int offset, int depth, boolean isFirst) {
		if(N <= 2) {
			return DFTN2(a, length, offset, depth, isFirst);
		}
		int newN = N >> 1;
		int newD = D << 1;
		long[][] a0 = FFTinverse(a, newD, newN, length << 1, offset, depth+1, true);
		long[][] a1 = FFTinverse(a, newD, newN, length << 1, offset+length, depth+1, false);
		long[][] c;
		if(isFirst) {
			if(TMP1[depth] == null) {
				TMP1[depth] = new long[N][2];
			}
			c = TMP1[depth];
		}
		else {
			if(TMP2[depth] == null) {
				TMP2[depth] = new long[N][2];
			}
			c = TMP2[depth];
		}
		c[0][0] = (a0[0][0] + a1[0][0]) % ClassicalPolynomial.P;
		c[0][1] = (a0[0][1] + a1[0][1]) % ClassicalPolynomial.P;
		c[newN][0] = (a0[0][0] - a1[0][0]) % ClassicalPolynomial.P;
		c[newN][1] = (a0[0][1] - a1[0][1]) % ClassicalPolynomial.P;
		int currD = D;
		long[] currOmega = ROOTS[ROOTS.length+currD];
		for(int i=1;i<newN;i++) {
			long[] tmp = ClassicalPolynomial.multiplication(a1[i], currOmega);
			c[i][0] = (tmp[0] + a0[i][0]) % ClassicalPolynomial.P;
			c[i][1] = (tmp[1] + a0[i][1]) % ClassicalPolynomial.P;
			c[i+newN][0] = (a0[i][0] - tmp[0]) % ClassicalPolynomial.P;
			c[i+newN][1] = (a0[i][1] - tmp[1]) % ClassicalPolynomial.P;
			currD += D;
			currOmega = ROOTS[ROOTS.length+currD];
		}
		return c;
	}
	
	private long[][] DFTN2(long[][] a, int length, int offset, int depth, boolean isFirst) {
		long[][] c;
		if(isFirst) {
			if(TMP1[depth] == null) {
				TMP1[depth] = new long[2][2];
			}
			c = TMP1[depth];
		}
		else {
			if(TMP2[depth] == null) {
				TMP2[depth] = new long[2][2];
			}
			c = TMP2[depth];
		}
		c[0][0] = (a[offset][0] + a[offset+length][0]) % ClassicalPolynomial.P;
		c[0][1] = (a[offset][1] + a[offset+length][1]) % ClassicalPolynomial.P;
		c[1][0] = (a[offset][0] - a[offset+length][0]) % ClassicalPolynomial.P;
		c[1][1] = (a[offset][1] - a[offset+length][1]) % ClassicalPolynomial.P;
		return c;
	}
	
	private void computeRoots(long[] omega, int N) {
		ROOTS = new long[N][2];
		ROOTS[0][0] = 1L;
		ROOTS[0][1] = 0L;
		for(int i=1;i<N;i++) {
			ROOTS[i] = ClassicalPolynomial.multiplication(omega, ROOTS[i-1]);
		}
	}
	
	private static long[] power(long[] a, long n) {
		if(n == 0) {
			return ClassicalPolynomial.ONE;
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
			result = ClassicalPolynomial.square(result);
			if((n & checkBit) == checkBit) {
				result = ClassicalPolynomial.multiplication(result, a);
			}
			checkBit >>= 1;
		}
		return result;
	}
	
	private static long[] multiplication(long[] a, long[] b) {
		long tmp1 = (a[0] * b[0]) % ClassicalPolynomial.P;
		long tmp2 = (a[1] * b[1]) % ClassicalPolynomial.P;
		tmp2 *= 3;
		tmp2 %= ClassicalPolynomial.P;
		tmp1 += tmp2;
		tmp1 %= ClassicalPolynomial.P;
		long tmp3 = (a[0] * b[1]) % ClassicalPolynomial.P;
		long tmp4 = (a[1] * b[0]) % ClassicalPolynomial.P;
		tmp3 += tmp4;
		tmp3 %= ClassicalPolynomial.P;
		long[] result = {tmp1, tmp3};
		return result;
	}
	
	private static long[] square(long[] a) {
		long tmp1 = (a[0] * a[0]) % ClassicalPolynomial.P;
		long tmp2 = (a[1] * a[1]) % ClassicalPolynomial.P;
		tmp2 *= 3;
		tmp2 %= ClassicalPolynomial.P;
		tmp1 += tmp2;
		tmp1 %= ClassicalPolynomial.P;
		long tmp3 = (a[0] * a[1]) % ClassicalPolynomial.P;
		tmp3 <<= 1;
		tmp3 %= ClassicalPolynomial.P;
		long[] result = {tmp1, tmp3};
		return result;
	}
}
