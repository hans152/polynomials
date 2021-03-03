These are the implementations of the algorithms for the multiplication of two polynomials with integer coefficients. To avoid computing in the complex numbers both algorithms compute in the field extension Z/pZ[sqrt(3)] for the Mersenne prime p=2^31-1. The corresponding paper can be found at https://arxiv.org/abs/
The first algorithm is a standard implementation of multiplication using an FFT algorithm and is only implemented for comparison. The second algorithm is the implementation of the algorithm presented in the paper.
