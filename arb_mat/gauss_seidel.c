/*=============================================================================

    This file is part of ARB.

    ARB is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    ARB is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with ARB; if not, write to the Free Software
    Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA

=============================================================================*/
/******************************************************************************

    Copyright (C) 2016 Arb authors

******************************************************************************/

#include "arb_mat.h"

int
_arb_mat_gauss_seidel_inplace(arb_mat_t X, const arb_mat_t A,
        const arb_mat_t B, slong prec)
{
    int result;
    slong i, n, m;

    if (!arb_mat_is_square(A))
    {
        flint_printf("_arb_mat_gauss_seidel_inplace: "
                     "a square matrix is required!\n");
        abort();
    }

    n = arb_mat_nrows(A);
    m = arb_mat_ncols(X);

    if (arb_mat_nrows(B) != n || arb_mat_ncols(B) != m ||
        arb_mat_nrows(X) != n)
    {
        flint_printf("_arb_mat_gauss_seidel_inplace: dimension mismatch\n");
        abort();
    }

    for (i = 0; i < n; i++)
    {
        if (arb_contains_zero(arb_mat_entry(A, i, i)))
        {
            flint_printf("gauss-seidel diagonal contains zero\n");
            abort();
            return 0;
        }
    }

    result = 1;
    {
        slong j, k;
        arb_t w, x, u;
        arb_mat_t P, U, V;

        /* precondition */
        arb_mat_init(P, n, n);
        arb_mat_init(U, n, n);
        arb_mat_init(V, n, m);
        arb_mat_set(P, A);
        for (i = 0; i < n; i++)
            for (j = 0; j < n; j++)
                mag_zero(arb_radref(arb_mat_entry(P, i, j)));
        arb_mat_inv(P, P, prec);
        for (i = 0; i < n; i++)
            for (j = 0; j < n; j++)
                mag_zero(arb_radref(arb_mat_entry(P, i, j)));
        arb_mat_mul(U, P, A, prec);
        arb_mat_mul(V, P, B, prec);

        arb_init(w);
        arb_init(x);
        arb_init(u);

        for (k = 0; k < m && result; k++)
        {
            for (i = 0; i < n && result; i++)
            {
                arb_set(w, arb_mat_entry(V, i, k));
                for (j = 0; j < n; j++)
                {
                    if (i != j)
                    {
                        /*
                        arb_set(u, arb_mat_entry(X, j, k));
                        arf_zero(arb_midref(u));
                        arb_addmul(w, arb_mat_entry(A, i, j), u, prec);
                        */
                        arb_submul(w, arb_mat_entry(U, i, j),
                                      arb_mat_entry(X, j, k), prec);
                    }
                }
                arb_div(w, w, arb_mat_entry(U, i, i), prec);

                /*
                arb_set(x, arb_mat_entry(X, i, k));
                mag_zero(arb_radref(x));
                arb_sub(x, x, w, prec);
                */
                arb_set(x, w);

                result = arb_intersection(arb_mat_entry(X, i, k),
                                          arb_mat_entry(X, i, k), x, prec);
                if (!result)
                {
                    flint_printf("gauss-seidel intersection fail\n");
                    arb_printd(arb_mat_entry(X, i, k), 15); flint_printf("\n");
                    arb_printd(x, 15); flint_printf("\n");
                    abort();
                }
            }
        }

        arb_mat_clear(P);
        arb_mat_clear(U);
        arb_mat_clear(V);

        arb_clear(w);
        arb_clear(x);
        arb_clear(u);
    }

    return result;
}

int
arb_mat_gauss_seidel(arb_mat_t Z, const arb_mat_t A,
        const arb_mat_t X, const arb_mat_t B, slong prec)
{
    arb_mat_set(Z, X);
    return _arb_mat_gauss_seidel_inplace(Z, A, B, prec);
}
