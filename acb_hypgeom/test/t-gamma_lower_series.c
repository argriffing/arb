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

#include "acb_poly.h"
#include "acb_hypgeom.h"

int main()
{
    slong iter;
    flint_rand_t state;

    flint_printf("gamma_lower_series....");
    fflush(stdout);

    flint_randinit(state);

    for (iter = 0; iter < 1000 * arb_test_multiplier(); iter++)
    {
        slong m, n1, n2, bits1, bits2, bits3;
        acb_poly_t S, A, B, C;
        acb_t s, t;

        bits1 = 2 + n_randint(state, 200);
        bits2 = 2 + n_randint(state, 200);
        bits3 = 2 + n_randint(state, 200);

        m = 1 + n_randint(state, 10);
        n1 = 1 + n_randint(state, 10);
        n2 = 1 + n_randint(state, 10);

        acb_poly_init(S);
        acb_poly_init(A);
        acb_poly_init(B);
        acb_poly_init(C);
        acb_init(s);
        acb_init(t);

        acb_poly_randtest(S, state, m, bits1, 3);
        acb_poly_randtest(A, state, m, bits1, 3);
        acb_poly_randtest(B, state, m, bits1, 3);
        acb_randtest(s, state, bits1, 3);

        acb_hypgeom_gamma_lower_series(A, s, S, n1, bits2);
        acb_hypgeom_gamma_lower_series(B, s, S, n2, bits3);

        acb_poly_set(C, A);
        acb_poly_truncate(C, FLINT_MIN(n1, n2));
        acb_poly_truncate(B, FLINT_MIN(n1, n2));

        if (!acb_poly_overlaps(B, C))
        {
            flint_printf("FAIL (consistency)\n\n");
            flint_printf("S = "); acb_poly_printd(S, 15); flint_printf("\n\n");
            flint_printf("A = "); acb_poly_printd(A, 15); flint_printf("\n\n");
            flint_printf("B = "); acb_poly_printd(B, 15); flint_printf("\n\n");
            abort();
        }

        acb_poly_derivative(C, S, bits2);
        acb_poly_neg(B, S);
        acb_poly_exp_series(B, B, n1, bits2);
        acb_poly_mullow(C, C, B, n1, bits2);
        acb_sub_ui(t, s, 1, bits2);
        acb_poly_pow_acb_series(B, S, t, n1, bits2);
        acb_poly_mullow(C, C, B, n1, bits2);
        acb_poly_truncate(C, n1 - 1);

        acb_poly_derivative(B, A, bits2);

        if (!acb_poly_overlaps(B, C))
        {
            flint_printf("FAIL (derivative)\n\n");
            flint_printf("S = "); acb_poly_printd(S, 15); flint_printf("\n\n");
            flint_printf("A = "); acb_poly_printd(A, 15); flint_printf("\n\n");
            flint_printf("B = "); acb_poly_printd(B, 15); flint_printf("\n\n");
            flint_printf("C = "); acb_poly_printd(C, 15); flint_printf("\n\n");
            abort();
        }

        acb_hypgeom_gamma_lower_series(S, s, S, n1, bits2);

        if (!acb_poly_overlaps(A, S))
        {
            flint_printf("FAIL (aliasing)\n\n");
            abort();
        }

        acb_poly_clear(S);
        acb_poly_clear(A);
        acb_poly_clear(B);
        acb_poly_clear(C);
        acb_clear(s);
        acb_clear(t);
    }

    flint_randclear(state);
    flint_cleanup();
    flint_printf("PASS\n");
    return EXIT_SUCCESS;
}
