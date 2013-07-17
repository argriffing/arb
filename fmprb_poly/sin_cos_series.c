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

    Copyright (C) 2013 Fredrik Johansson

******************************************************************************/

#include "fmprb_poly.h"

#define TANGENT_CUTOFF 20

void
_fmprb_poly_sin_cos_series(fmprb_ptr s, fmprb_ptr c, const fmprb_srcptr h, long hlen, long len, long prec)
{
    if (hlen < TANGENT_CUTOFF)
        _fmprb_poly_sin_cos_series_basecase(s, c, h, hlen, len, prec);
    else
        _fmprb_poly_sin_cos_series_tangent(s, c, h, hlen, len, prec);
}

void
fmprb_poly_sin_cos_series(fmprb_poly_t s, fmprb_poly_t c,
                                    const fmprb_poly_t h, long n, long prec)
{
    long hlen = h->length;

    if (n == 0)
    {
        fmprb_poly_zero(s);
        fmprb_poly_zero(c);
        return;
    }

    if (hlen == 0)
    {
        fmprb_poly_zero(s);
        fmprb_poly_one(c);
        return;
    }

    fmprb_poly_fit_length(s, n);
    fmprb_poly_fit_length(c, n);
    _fmprb_poly_sin_cos_series(s->coeffs, c->coeffs, h->coeffs, hlen, n, prec);
    _fmprb_poly_set_length(s, n);
    _fmprb_poly_normalise(s);
    _fmprb_poly_set_length(c, n);
    _fmprb_poly_normalise(c);
}

