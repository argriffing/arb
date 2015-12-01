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

    Copyright (C) 2015 Arb authors

******************************************************************************/

#include "arb_mat.h"

void
arb_mat_mul_entrywise(arb_mat_t C, const arb_mat_t A, const arb_mat_t B, slong prec)
{
    slong ar, ac, i, j;

    ar = arb_mat_nrows(A);
    ac = arb_mat_ncols(A);

    if (ar != arb_mat_nrows(B) || ac != arb_mat_ncols(B) ||
        ar != arb_mat_nrows(C) || ac != arb_mat_nrows(C))
    {
        flint_printf("arb_mat_mul_entrywise: incompatible dimensions\n");
        abort();
    }

    for (i = 0; i < nr; i++)
    {
        for (j = 0; j < nc; j++)
        {
            arb_mul(arb_mat_entry(C, i, j),
                    arb_mat_entry(A, i, j),
                    arb_mat_entry(B, i, j), prec);
        }
    }
}
