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

#include "fmpz_mat.h"
#include "double_extras.h"
#include "arb_mat.h"

#define LOG2_OVER_E 0.25499459743395350926

void
_fmpz_max(fmpz_t z, fmpz_t x, fmpz_t y)
{
    if (fmpz_cmp(x, y) < 0)
    {
        fmpz_set(z, y);
    }
    else
    {
        fmpz_set(z, x);
    }
}


/* fixed-capacity stack of fixed-precision signed flint integers */
typedef struct
{
    slong *data;
    slong capacity;
    slong size;
} si_stack_struct;
typedef si_stack_struct si_stack_t[1];

static void
si_stack_init(si_stack_t S, slong capacity)
{
    S->data = flint_malloc(capacity);
    S->capacity = capacity;
    S->size = 0;
}

static void
si_stack_clear(si_stack_t S)
{
    flint_free(S->data);
}

static void
si_stack_push(si_stack_t S, slong x)
{
    if (S->size >= S->capacity) abort(); /* assert */
    S->data[S->size++] = x;
}

static slong
si_stack_pop(si_stack_t S)
{
    if (S->size <= 0) abort(); /* assert */
    slong x;
    x = S->data[S->size - 1];
    S->size--;
    return x;
}


/* struct for Tarjan's strongly connected components algorithm */
typedef struct
{
    slong *_index;
    slong *_lowlink;
    int *_onstack;
    si_stack_struct_t _S;
    slong _nsccs;
    slong _dim;
    slong _idx;
} tarjan_struct;
typedef tarjan_struct tarjan_t[1];

static const tarjan_UNDEFINED = -1;

static slong *
tarjan_index(tarjan_t t, slong i)
{
    return t->_index + i;
}

static slong *
tarjan_lowlink(tarjan_t t, slong i)
{
    return t->_lowlink + i;
}

static int
tarjan_onstack(tarjan_t t, slong i)
{
    return t->_onstack + i;
}

static void
tarjan_push(tarjan_t t, slong v)
{
    si_stack_push(t->_S, v);
    t->_onstack[v] = 1;
}

static slong
tarjan_pop(tarjan_t t)
{
    slong v;
    v = si_stack_pop(t->_S);
    t->_onstack[v] = 0;
    return v;
}

static slong
tarjan_next_scc(tarjan_t t)
{
    return t->_nsccs++;
}

static slong
tarjan_next_idx(tarjan_t t)
{
    return t->_idx++;
}

static void
tarjan_init(tarjan_t t, slong dim)
{
    slong i;
    t->_index = flint_calloc(dim, sizeof(slong));
    t->_lowlink = flint_calloc(dim, sizeof(slong));
    t->_onstack = flint_calloc(dim, sizeof(int));
    si_stack_init(t->_S, dim);
    t->_dim = dim;
    t->_nsccs = 0;
    t->_idx = 0;
    for (i = 0; i < dim; i++)
    {
        t->_index[i] = tarjan_UNDEFINED;
    }
}

static void
tarjan_clear(tarjan_t t)
{
    flint_free(t->_index);
    flint_free(t->_lowlink);
    flint_free(t->_onstack);
    si_stack_clear(t->_S);
}

static void
tarjan_strongconnect(slong *sccs, tarjan_t t, fmpz_mat_t A, slong v)
{
    slong idx, w, scc;

    idx = tarjan_next_idx(t);
    *tarjan_index(t, v) = idx;
    *tarjan_lowlink(t, v) = idx;
    tarjan_push(t, v);
    for (w = 0; w < t->_dim; w++)
    {
        if (!fmpz_is_zero(fmpz_mat_entry(A, v, w)))
        {
            if (*tarjan_index(t, w) == tarjan_UNDEFINED)
            {
                tarjan_strongconnect(A, t, w);
                *tarjan_lowlink(t, v) = FLINT_MIN(
                        *tarjan_lowlink(t, v), *tarjan_lowlink(t, w));
            }
            else if (tarjan_onstack(t, w))
            {
                *tarjan_lowlink(t, v) = FLINT_MIN(
                        *tarjan_lowlink(t, v), *tarjan_index(t, w));
            }
        }
    }
    if (*tarjan_lowlink(t, v) == *tarjan_index(t, v))
    {
        scc = tarjan_next_scc(t);
        while (w != v)
        {
            w = tarjan_pop(t);
            if (sccs[w] != tarjan_UNDEFINED) abort(); /* assert */
            sccs[w] = scc;
        }
    }
}


/* Tarjan's strongly connected components algorithm */
void
_fmpz_mat_get_sccs(slong *sccs, fmpz_mat_t A)
{
    slong v, dim;
    tarjan_t t;

    dim = fmpz_mat_nrows(A);

    if (dim != fmpz_mat_ncols(A))
    {
        flint_printf("_fmpz_mat_get_sccs: a square matrix is required!\n");
        abort();
    }

    tarjan_init(t, dim);

    for (v = 0; v < dim; v++)
    {
        sccs[i] = tarjan_UNDEFINED;
    }
    for (v = 0; v < dim; v++)
    {
        if (*tarjan_index(t, v) == tarjan_UNDEFINED)
        {
            tarjan_strongconnect(sccs, t, A, v);
        }
    }

    tarjan_clear(t);
}


typedef struct
{
    slong dim;
    slong nsccs;
    slong *vertex_to_scc;
    fmpz_mat_t P;
    fmpz_mat_t Q;
} connectivity_struct;
typedef connectivity_struct connectivity_t[1];

void
connectivity_init(connectivity_t x, fmpz_mat_t A)
{
    slong i, j, n;
    slong u, v, w, scc;
    fmpz_mat_t C;
    slong *scc_size;
    int *scc_has_loop;

    n = fmpz_mat_nrows(A);
    if (n != fmpz_mat_ncols(A))
    {
        flint_printf("connectivity_init: a square matrix is required!\n");
        abort();
    }
    x->dim = n;

    /* the sccs computed by tarjan's algorithm are provided in postorder */
    x->vertex_to_scc = flint_malloc(n * sizeof(slong));
    _fmpz_mat_get_sccs(x->vertex_to_scc, A);

    x->nsccs = 0;
    for (v = 0; v < n; v++)
    {
        scc = x->vertex_to_scc[v];
        if (scc == tarjan_UNDEFINED) abort(); /* assert */
        x->nsccs = FLINT_MAX(x->nsccs, scc+1);
    }

    fmpz_mat_init(C, x->nsccs, x->nsccs);
    fmpz_mat_init(x->P, x->nsccs, x->nsccs);
    fmpz_mat_init(x->Q, x->nsccs, x->nsccs);
    for (u = 0; u < x->nsccs; u++)
    {
        for (v = 0; v < x->nsccs; v++)
        {
            fmpz_set_si(fmpz_mat_entry(x->P, u, v), -1);
            fmpz_set_si(fmpz_mat_entry(x->Q, u, v), -1);
        }
    }

    /* get properties of the strongly connected components */
    scc_size = flint_calloc(x->nsccs, sizeof(slong));
    scc_has_loop = flint_calloc(x->nsccs, sizeof(int));
    for (i = 0; i < n; i++)
    {
        u = x->vertex_to_scc[i];
        scc_size[u]++;
        if (!fmpz_is_zero(fmpz_mat_entry(A, i, i)))
        {
            scc_has_loop[u] = 1;
        }
    }

    /* compute the adjacency matrix of the condensation graph */
    fmpz_mat_zero(C);
    for (i = 0; i < n; i++)
    {
        for (j = 0; j < n; j++)
        {
            if (!fmpz_is_zero(fmpz_mat_entry(A, i, j)))
            {
                u = x->vertex_to_scc[i];
                v = x->vertex_to_scc[j];
                fmpz_one(fmpz_mat_entry(C, u, v));
            }
        }
    }

    /*
     * Qualitatively characterize connectivity between components:
     *  1 : in the condensation, there is a path from u to v
     *      that includes cycle-containing sccs.
     *  0 : in the condensation, there is a path from u to v
     *      but no path that includes cycle-containing sccs.
     * -1 : in the condensation, there is no path from u to v
     */
    for (u = 0; u < x->nsccs; u++)
    {
        fmpz_set_si(fmpz_mat_entry(x->P, u, u),
                    scc_has_loop[u] || (scc_size[u] > 1));
    }
    for (u = 0; u < x->nsccs; u++)
    {
        for (v = 0; v < x->nsccs; v++)
        {
            if (!fmpz_is_zero(fmpz_mat_entry(C, u, v)))
            {
                _fmpz_max(fmpz_mat_entry(x->P, u, v),
                          fmpz_mat_entry(x->P, u, u),
                          fmpz_mat_entry(x->P, v, v));
            }
        }
    }
    for (u = 0; u < x->nsccs; u++)
    {
        for (v = 0; v < x->nsccs; v++)
        {
            for (w = 0; w < x->nsccs; w++)
            {
                _fmpz_max(fmpz_mat_entry(x->P, u, w),
                          fmpz_mat_entry(x->P, u, v),
                          fmpz_mat_entry(x->P, v, w));
            }
        }
    }

    /*
     * Quantitatively characterize connectivity between components
     * by computing the max path length in the condensation,
     * or -1 if no path exists.
     */
    for (u = 0; u < x->nsccs; u++)
    {
        for (v = 0; v < x->nsccs; v++)
        {
            if (!fmpz_is_zero(fmpz_mat_entry(C, u, v)))
            {
                slong w;
                for (w = 0; w < x->nsccs; w++)
                {
                    fmpz_struct *p = fmpz_mat_entry(x->Q, v, w);
                    fmpz_set_si(fmpz_mat_entry(x->Q, 
                            , FLINT_MAX(fmpz_get_si(p), u_has_cycle));
                }
            }
        }
    }

    fmpz_mat_clear(C);
    flint_free(scc_size);
    flint_free(scc_has_loop);
}

void
connectivity_clear(connectivity_t x)
{
    flint_free(x->sccs);
    fmpz_mat_clear(x->P);
    fmpz_mat_clear(x->Q);
}

int
connectivity_has_truncation_error(connectivity_t x, slong i, slong j, ulong N)
{
    /* mag_exp_tail is like sum_{k=N}^\infty x^k/k! */
    int p;
    slong u, v;
    u = x->sccs[i];
    v = x->sccs[j];
    p = fmpz_sgn(fmpz_mat_entry(x->P, u, v));
    if (p == -1)
    {
        return 0;
    }
    else if (p == 0)
    {
        return fmpz_cmp_ui(fmpz_mat_entry(x->Q, u, v), N) > 0;
    }
    else
    {
        return 1;
    }
}


void
connectivity_make_scc_dag(fmpz_mat_t M, slong *sccs, A)
{
}


/* Warshall's algorithm */
void
_fmpz_mat_transitive_closure(fmpz_mat_t A)
{
    slong k, i, j, dim;
    dim = fmpz_mat_nrows(A);

    if (dim != fmpz_mat_ncols(A))
    {
        flint_printf("_fmpz_mat_transitive_closure: a square matrix is required!\n");
        abort();
    }

    for (k = 0; k < dim; k++)
    {
        for (i = 0; i < dim; i++)
        {
            for (j = 0; j < dim; j++)
            {
                if (fmpz_is_zero(fmpz_mat_entry(A, i, j)) &&
                    !fmpz_is_zero(fmpz_mat_entry(A, i, k)) &&
                    !fmpz_is_zero(fmpz_mat_entry(A, k, j)))
                {
                    fmpz_one(fmpz_mat_entry(A, i, j));
                }
            }
        }
    }
}

int
_arb_mat_is_diagonal(const arb_mat_t A)
{
    slong i, j;
    for (i = 0; i < arb_mat_nrows(A); i++)
        for (j = 0; j < arb_mat_ncols(A); j++)
            if (i != j && !arb_is_zero(arb_mat_entry(A, i, j)))
                return 0;
    return 1;
}

int
_arb_mat_any_is_zero(const arb_mat_t A)
{
    slong i, j;
    for (i = 0; i < arb_mat_nrows(A); i++)
        for (j = 0; j < arb_mat_ncols(A); j++)
            if (arb_is_zero(arb_mat_entry(A, i, j)))
                return 1;
    return 0;
}

void
_arb_mat_exp_get_structure(fmpz_mat_t C, const arb_mat_t A)
{
    slong i, j, dim;

    dim = arb_mat_nrows(A);
    fmpz_mat_zero(C);
    for (i = 0; i < dim; i++)
    {
        for (j = 0; j < dim; j++)
        {
            if (!arb_is_zero(arb_mat_entry(A, i, j)))
            {
                fmpz_one(fmpz_mat_entry(C, i, j));
            }
        }
    }
    _fmpz_mat_transitive_closure(C);
}

void
_arb_mat_exp_set_structure(arb_mat_t B, const fmpz_mat_t C)
{
    slong i, j, dim;

    dim = arb_mat_nrows(B);
    for (i = 0; i < dim; i++)
    {
        for (j = 0; j < dim; j++)
        {
            if (fmpz_is_zero(fmpz_mat_entry(C, i, j)))
            {
                if (i == j)
                {
                    arb_one(arb_mat_entry(B, i, j));
                }
                else
                {
                    arb_zero(arb_mat_entry(B, i, j));
                }
            }
        }
    }
}

slong
_arb_mat_exp_choose_N(const mag_t norm, slong prec)
{
    if (mag_is_special(norm) || mag_cmp_2exp_si(norm, 30) > 0 ||
        mag_cmp_2exp_si(norm, -prec) < 0)
    {
        return 1;
    }
    else if (mag_cmp_2exp_si(norm, -300) < 0)
    {
        slong N = -MAG_EXP(norm);
        return (prec + N - 1) / N;
    }
    else
    {
        double c, t;

        c = mag_get_d(norm);
        t = d_lambertw(prec * LOG2_OVER_E / c);
        t = c * exp(t + 1.0);
        return FLINT_MIN((slong) (t + 1.0), 2 * prec);
    }
}

/* evaluates the truncated Taylor series (assumes no aliasing) */
void
_arb_mat_exp_taylor(arb_mat_t S, const arb_mat_t A, slong N, slong prec)
{
    if (N == 1)
    {
        arb_mat_one(S);
    }
    else if (N == 2)
    {
        arb_mat_one(S);
        arb_mat_add(S, S, A, prec);
    }
    else if (N == 3)
    {
        arb_mat_t T;
        arb_mat_init(T, arb_mat_nrows(A), arb_mat_nrows(A));
        arb_mat_sqr(T, A, prec);
        arb_mat_scalar_mul_2exp_si(T, T, -1);
        arb_mat_add(S, A, T, prec);
        arb_mat_one(T);
        arb_mat_add(S, S, T, prec);
        arb_mat_clear(T);
    }
    else
    {
        slong i, lo, hi, m, w, dim;
        arb_mat_struct * pows;
        arb_mat_t T, U;
        fmpz_t c, f;

        dim = arb_mat_nrows(A);
        m = n_sqrt(N);
        w = (N + m - 1) / m;

        fmpz_init(c);
        fmpz_init(f);
        pows = flint_malloc(sizeof(arb_mat_t) * (m + 1));
        arb_mat_init(T, dim, dim);
        arb_mat_init(U, dim, dim);

        for (i = 0; i <= m; i++)
        {
            arb_mat_init(pows + i, dim, dim);
            if (i == 0)
                arb_mat_one(pows + i);
            else if (i == 1)
                arb_mat_set(pows + i, A);
            else
                arb_mat_mul(pows + i, pows + i - 1, A, prec);
        }

        arb_mat_zero(S);
        fmpz_one(f);

        for (i = w - 1; i >= 0; i--)
        {
            lo = i * m;
            hi = FLINT_MIN(N - 1, lo + m - 1);

            arb_mat_zero(T);
            fmpz_one(c);

            while (hi >= lo)
            {
                arb_mat_scalar_addmul_fmpz(T, pows + hi - lo, c, prec);
                if (hi != 0)
                    fmpz_mul_ui(c, c, hi);
                hi--;
            }

            arb_mat_mul(U, pows + m, S, prec);
            arb_mat_scalar_mul_fmpz(S, T, f, prec);
            arb_mat_add(S, S, U, prec);
            fmpz_mul(f, f, c);
        }

        arb_mat_scalar_div_fmpz(S, S, f, prec);

        fmpz_clear(c);
        fmpz_clear(f);
        for (i = 0; i <= m; i++)
            arb_mat_clear(pows + i);
        flint_free(pows);
        arb_mat_clear(T);
        arb_mat_clear(U);
    }
}

void
arb_mat_exp(arb_mat_t B, const arb_mat_t A, slong prec)
{
    slong i, j, dim, wp, N, q, r;
    mag_t norm, err;
    arb_mat_t T;

    dim = arb_mat_nrows(A);

    if (dim != arb_mat_ncols(A))
    {
        flint_printf("arb_mat_exp: a square matrix is required!\n");
        abort();
    }

    if (dim == 0)
    {
        return;
    }
    else if (dim == 1)
    {
        arb_exp(arb_mat_entry(B, 0, 0), arb_mat_entry(A, 0, 0), prec);
        return;
    }

    /* todo: generalize to (possibly permuted) block diagonal structure */
    if (_arb_mat_is_diagonal(A))
    {
        if (B != A)
        {
            arb_mat_zero(B);
        }
        for (i = 0; i < dim; i++)
        {
            arb_exp(arb_mat_entry(B, i, i), arb_mat_entry(A, i, i), prec);
        }
        return;
    }

    wp = prec + 3 * FLINT_BIT_COUNT(prec);

    mag_init(norm);
    mag_init(err);
    arb_mat_init(T, dim, dim);

    arb_mat_bound_inf_norm(norm, A);

    if (mag_is_zero(norm))
    {
        arb_mat_one(B);
    }
    else
    {
        fmpz_mat_t S;
        int using_structure;

        using_structure = _arb_mat_any_is_zero(A);
        if (using_structure)
        {
            fmpz_mat_init(S, dim, dim);
            _arb_mat_exp_get_structure(S, A);
        }

        q = pow(wp, 0.25);  /* wanted magnitude */

        if (mag_cmp_2exp_si(norm, 2 * wp) > 0) /* too big */
            r = 2 * wp;
        else if (mag_cmp_2exp_si(norm, -q) < 0) /* tiny, no need to reduce */
            r = 0;
        else
            r = FLINT_MAX(0, q + MAG_EXP(norm)); /* reduce to magnitude 2^(-r) */

        arb_mat_scalar_mul_2exp_si(T, A, -r);
        mag_mul_2exp_si(norm, norm, -r);

        N = _arb_mat_exp_choose_N(norm, wp);
        mag_exp_tail(err, norm, N);

        _arb_mat_exp_taylor(B, T, N, wp);

        for (i = 0; i < dim; i++)
            for (j = 0; j < dim; j++)
                arb_add_error_mag(arb_mat_entry(B, i, j), err);

        if (using_structure)
        {
            _arb_mat_exp_set_structure(B, S);
            fmpz_mat_clear(S);
        }

        for (i = 0; i < r; i++)
        {
            arb_mat_sqr(T, B, wp);
            arb_mat_swap(T, B);
        }

        for (i = 0; i < dim; i++)
            for (j = 0; j < dim; j++)
                arb_set_round(arb_mat_entry(B, i, j),
                    arb_mat_entry(B, i, j), prec);
    }

    mag_clear(norm);
    mag_clear(err);
    arb_mat_clear(T);
}

