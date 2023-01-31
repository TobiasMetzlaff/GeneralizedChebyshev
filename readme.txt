This is a Maple 2022 package for computations with generalized Chebyshev polynomials [1] associated to weight lattices of crystallographic root systems [2].

The main purpose of this package is to produce matrices for semi-definite programs that appear in polynomial optimization [3].



Next to this 'readme.txt', you have received two files 'GeneralizedChebsyhev.mpl' and 'GeneralizedChebsyhevHelp.mw'.

After extraction, place both in the same folder, start Maple2022 and open the file 'GeneralizedChebsyhevHelp.mw'.

The worksheet 'GeneralizedChebsyhevHelp.mw' is a guide through the available commands of the package.

The first time running 
 read("GeneralizedChebyshev.mpl"): with(GeneralizedChebyshev);
can return an error. In this case, save the file, close it and open it again.

To use 'GeneralizedChebsyhevHelp.mw' in any Maple 2022 worksheet, place it in the same folder as the worksheet and run the above command.



For questions, please contact 'tobias.metzlaff@inria.fr'.



[1] M. Hoffman and W. Withers: Generalized Chebyshev Polynomials Associated with Affine Weyl Groups.
https://www.jstor.org/stable/2000951#metadata_info_tab_contents

[2] Bourbaki: Groupes et algèbres de Lie, Ch. VI.
https://link.springer.com/book/10.1007/978-3-540-34491-9

[3] E. Hubert, T. Metzlaff, P. Moustrou and C. Riener: Optimization of trigonometric polynomials with crystallographic symmetry and applications.
https://hal.science/hal-03768067v1
