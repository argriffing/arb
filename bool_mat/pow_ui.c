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

#include "bool_mat.h"

void
bool_mat_pow_ui(bool_mat_t B, const bool_mat_t A, ulong exp)
{
    slong d;

    if (!bool_mat_is_square(A))
    {
        flint_printf("bool_mat_pow_ui: a square matrix is required!\n");
        abort();
    }

    if (bool_mat_is_empty(A))
        return;

    d = bool_mat_nrows(A);

    if (exp <= 2 || d <= 1)
    {
        if (exp == 0)
        {
            bool_mat_one(B);
        }
        else if (d == 1)
        {
            *bool_mat_entry(B, 0, 0) = *bool_mat_entry(A, 0, 0);
        }
        else if (exp == 1)
        {
            bool_mat_set(B, A);
        }
        else if (exp == 2)
        {
            bool_mat_sqr(B, A);
        }
    }
    else
    {
        slong i;
        bool_mat_t T, U;

        bool_mat_init(T, d, d);
        bool_mat_set(T, A);
        bool_mat_init(U, d, d);

        for (i = ((slong) FLINT_BIT_COUNT(exp)) - 2; i >= 0; i--)
        {
            bool_mat_sqr(U, T);

            if (exp & (WORD(1) << i))
                bool_mat_mul(T, U, A);
            else
                bool_mat_swap(T, U);
        }

        bool_mat_swap(B, T);
        bool_mat_clear(T);
        bool_mat_clear(U);
    }
}