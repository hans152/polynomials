/**
 * 
 * @author Andreas Rosowski
 *
 */
public class ClassicalPolynomial {
	private static final long P = 2147483647L;
	private static final long[] ONE = {1L, 0L};
	
	public long[] mult(long[] a, long[] b) {
		int N = a.length + b.length - 1;
		int d = 0;
		while(N > 0) {
			d++;
			N >>= 1;
		}
		N = 1 << d;
		long[] omega = {2L, 1L};
		omega = ClassicalPolynomial.power(omega, (ClassicalPolynomial.P + 1) >> d);
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
		aTmp = FFT(aTmp, omega, N);
		bTmp = FFT(bTmp, omega, N);
		long[][] cTmp = new long[N][2];
		for(int i=0;i<N;i++) {
			cTmp[i] = ClassicalPolynomial.multiplication(aTmp[i], bTmp[i]);
		}
		omega = ClassicalPolynomial.power(omega, N-1);
		cTmp = FFT(cTmp, omega, N);
		long[] c = new long[a.length + b.length - 1];
		long[] inverseN = {(ClassicalPolynomial.P + 1) >> d, 0L};
		for(int i=0;i<c.length;i++) {
			long[] tmp = ClassicalPolynomial.multiplication(cTmp[i], inverseN);
			c[i] = (tmp[0] + ClassicalPolynomial.P) % ClassicalPolynomial.P;
		}
		return c;
	}
	
	private long[][] FFT(long[][] a, long[] omega, int N) {
		if(N <= 4) {
			return DFT(a, omega, N);
		}
		int newN = N >> 1;
		long[] newOmega = ClassicalPolynomial.square(omega);
		long[][] a0 = new long[newN][2];
		for(int i=0;i<newN;i++) {
			a0[i] = a[i << 1];
		}
		a0 = FFT(a0, newOmega, newN);
		long[][] a1 = new long[newN][2];
		for(int i=0;i<newN;i++) {
			a1[i] = a[(i << 1) + 1];
		}
		a1 = FFT(a1, newOmega, newN);
		long[][] c = new long[N][2];
		c[0][0] = (a0[0][0] + a1[0][0]) % ClassicalPolynomial.P;
		c[0][1] = (a0[0][1] + a1[0][1]) % ClassicalPolynomial.P;
		c[newN][0] = (a0[0][0] - a1[0][0]) % ClassicalPolynomial.P;
		c[newN][1] = (a0[0][1] - a1[0][1]) % ClassicalPolynomial.P;
		long[] currOmega = omega;
		for(int i=1;i<newN;i++) {
			long[] tmp = ClassicalPolynomial.multiplication(a1[i], currOmega);
			c[i][0] = (tmp[0] + a0[i][0]) % ClassicalPolynomial.P;
			c[i][1] = (tmp[1] + a0[i][1]) % ClassicalPolynomial.P;
			c[i+newN][0] = (a0[i][0] - tmp[0]) % ClassicalPolynomial.P;
			c[i+newN][1] = (a0[i][1] - tmp[1]) % ClassicalPolynomial.P;
			currOmega = ClassicalPolynomial.multiplication(currOmega, omega);
		}
		return c;
	}
	
	private long[][] DFT(long[][] a, long[] omega, int N) {
		long[] currOmega = ClassicalPolynomial.ONE;
		long[] toMultiplyOmega = ClassicalPolynomial.ONE;
		long[][] c = new long[N][2];
		for(int i=0;i<N;i++) {
			for(int j=0;j<N;j++) {
				long[] tmp = ClassicalPolynomial.multiplication(a[j], currOmega);
				c[i][0] += tmp[0];
				c[i][1] += tmp[1];
				currOmega = ClassicalPolynomial.multiplication(currOmega, toMultiplyOmega);
			}
			c[i][0] %= ClassicalPolynomial.P;
			c[i][1] %= ClassicalPolynomial.P;
			toMultiplyOmega = ClassicalPolynomial.multiplication(toMultiplyOmega, omega);
			currOmega = ClassicalPolynomial.ONE;
		}
		return c;
	}
	
	private static long[] power(long[] a, long n) {
		long[] result = new long[2];
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
		result = a;
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
