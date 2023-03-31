This is a Maple 2022 (https://de.maplesoft.com/products/maple/) package for computations with generalized Chebyshev polynomials associated to the simple Lie algebras.

The main purpose of this package is to produce matrices for semi-definite programs that appear in polynomial optimization [4].
Beyond that, it features several functionalities for computations with Weyl groups of simple Lie type and polynomial descriptions for the orbit space [5].

If you are specifically interested in Weyl groups acting on minuscule weights:
Those are not covered here (yet), but there is a Maple 2008 worksheet by Michael Singer (https://singer.math.ncsu.edu/papers/minuscule/).


Definition:

A Euclidean reflection group W that leaves a full-dimensional lattice Omega invariant is called Weyl group.
The reflections can be defined through a crystallographic root system, which is a set of points with "nice" properties in the sense of [1,2,3].
The invariant lattice  is spanned by the fundamental weights omega_1...omega_n of the root system and also called weight lattice.
A theorem from multiplicative invariant theory states that those elements of the group ring Q[Omega], which are invariant under the induced action of W, form a polynomial algebra:
 
(*) Q[Omega]^W = Q[theta_{omega_1}, ..., theta_{omega_n}],

where for every weight in Omega we define the "orbit polynomial" or "generalized cosine"

    theta_weight := 1/|W| \sum\limits_{A \in W} e^{A weight}.
    
The property (*) allows to define the generalized Chebyshev polynomial (of the first kind) associated to a weight, namely the unique multivariate T_weight in Q[z_1, ..., z_n], such that

    T_weight(theta_{omega_1}, ..., theta_{omega_n}) = theta_weight.

These polynomials form a basis of Q[z_1, ..., z_n] and are orthogonal on the orbit space of W, that is, on the basic semi-algebraic set

    TOrbSpace := { (theta_{omega_1}, ..., theta_{omega_n})(u) | u in R^n }.

In [5], we have constructed a Hermite matrix polynomial H with the property

    TOrbSpace = { z in R^n | H(z) is positive semi-definite}.
    
The matrix entries of H are given through a closed formula that is available as a command in the package.

Any root system can be decomposed into irreducible components which classify the 7 families of simple Lie algebras:

    A B C (n>=2)    D (n>=4)    E (n=6,7,8)    F (n=4)    G (n=2)

Any semi-simple Lie algebra admits a root system that decomposes into orthogonal, irreducible components which are of one of the above "simple Lie types". Hence, we only need to consider the latter.


Installation:

Download the two files 'GeneralizedChebsyhev.mpl' and 'GeneralizedChebsyhevHelp.mw'.
Place both in the SAME folder open the file 'GeneralizedChebsyhevHelp.mw' with Maple2022.
The worksheet 'GeneralizedChebsyhevHelp.mw' is a guide through the available commands of the package.
The first time running 

    read("GeneralizedChebyshev.mpl"): 
    with(GeneralizedChebyshev);

can output an error. In this case, save everything, close Maple and reopen it.
To use 'GeneralizedChebsyhevHelp.mw' in any other Maple 2022 worksheet, place it in the same folder as the worksheet and run the above command.


Problems/Questions:

Feel free to contact 'tobias.metzlaff@rptu.de'.


Literature:

[1] Bourbaki: Groupes et algèbres de Lie.
https://link.springer.com/book/10.1007/978-3-540-34491-9

[2] J. E. Humphreys: Introduction to Lie algebras and representation theory
https://link.springer.com/book/10.1007/978-1-4612-6398-2

[3] R. Kane: Reflection groups and invariant theory
https://link.springer.com/chapter/10.1007/978-1-4757-3542-0_1

[4] E. Hubert, T. Metzlaff, P. Moustrou and C. Riener: Optimization of trigonometric polynomials with crystallographic symmetry and spectral bounds for set avoiding graphs.
https://hal.science/hal-03768067

[5] E. Hubert, T. Metzlaff, and C. Riener: Polynomial description for the T-orbit spaces of multiplicative actions.
https://hal.science/hal-03590007
