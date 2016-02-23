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

int
_arb_gt_si(arb_t a, slong b)
{
    int result;
    arb_t c;
    arb_init(c);
    arb_set_si(c, b);
    result = arb_gt(a, c);
    arb_clear(c);
    return result;
}

int
_arb_lt_si(arb_t a, slong b)
{
    int result;
    arb_t c;
    arb_init(c);
    arb_set_si(c, b);
    result = arb_lt(a, c);
    arb_clear(c);
    return result;
}

void
_arb_max_exact(arb_t z, const arb_t x, const arb_t y)
{
    if (!arb_is_exact(x)) abort();
    if (!arb_is_exact(y)) abort();
    if (arb_lt(x, y))
    {
        arb_set(z, y);
    }
    else
    {
        arb_set(z, x);
    }
}

void
_arb_mat_max_exact(arb_t x, arb_mat_t A)
{
    slong i, j;
    arb_set(x, arb_mat_entry(A, 0, 0));
    for (i = 0; i < arb_mat_nrows(A); i++)
        for (j = 0; j < arb_mat_ncols(A); j++)
            _arb_max_exact(x, x, arb_mat_entry(A, i, j));
}

/* Warshall's algorithm */
void
_fmpz_mat_transitive_closure(fmpz_mat_t B, fmpz_mat_t A)
{
    slong k, i, j, dim;
    dim = fmpz_mat_nrows(A);

    if (dim != fmpz_mat_ncols(A))
    {
        flint_printf("_fmpz_mat_transitive_closure: a square matrix is required!\n");
        abort();
    }

    if (B != A)
    {
        fmpz_mat_set(B, A);
    }

    for (k = 0; k < dim; k++)
    {
        for (i = 0; i < dim; i++)
        {
            for (j = 0; j < dim; j++)
            {
                if (fmpz_is_zero(fmpz_mat_entry(B, i, j)) &&
                    !fmpz_is_zero(fmpz_mat_entry(B, i, k)) &&
                    !fmpz_is_zero(fmpz_mat_entry(B, k, j)))
                {
                    fmpz_one(fmpz_mat_entry(B, i, j));
                }
            }
        }
    }
}

int
_fmpz_mat_is_strict_lower_triangular(const fmpz_mat_t A)
{
    slong i, j;
    for (i = 0; i < fmpz_mat_nrows(A); i++)
    {
        for (j = 0; j < fmpz_mat_ncols(A); j++)
        {
            if (i <= j)
            {
                if (!fmpz_is_zero(fmpz_mat_entry(A, i, j)))
                {
                    return 0;
                }
            }
        }
    }
    return 1;
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
    S->data = flint_malloc(capacity * sizeof(slong));
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
    slong x;
    if (S->size <= 0) abort(); /* assert */
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
    si_stack_t _S;
    slong _nsccs;
    slong _dim;
    slong _idx;
} tarjan_struct;
typedef tarjan_struct tarjan_t[1];

static const slong tarjan_UNDEFINED = -1;

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
    return t->_onstack[i];
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
                tarjan_strongconnect(sccs, t, A, w);
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
        sccs[v] = tarjan_UNDEFINED;
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


/*
 * Condensation of a matrix.
 * This is the directed acyclic graph of strongly connected components.
 */
typedef struct
{
    slong n; /* number of vertices in the original graph */
    slong k; /* number of strongly connnected components (sccs) */
    fmpz_mat_t C; /* adjacency matrix of the sccs in the condensation */
    slong *partition; /* maps the vertex index to the scc index */
} condensation_struct;

typedef condensation_struct condensation_t[1];

void
condensation_fprint(FILE * file, condensation_t c)
{
    slong i;
    flint_fprintf(file, "number of vertices: %wd\n", c->n);
    flint_fprintf(file, "number of SCCs: %wd\n", c->k);
    flint_fprintf(file, "adjacency matrix of SCCs:\n");
    fmpz_mat_fprint_pretty(file, c->C);
    flint_fprintf(file, "\n");
    flint_fprintf(file, "partition of vertices:\n");
    for (i = 0; i < c->n; i++)
    {
        flint_fprintf(file, "%wd : %wd\n", i, c->partition[i]);
    }
}

void
condensation_init(condensation_t c, fmpz_mat_t A)
{
    slong i, j, u, v;

    c->n = fmpz_mat_nrows(A);
    if (c->n != fmpz_mat_ncols(A))
    {
        flint_printf("condensation_init: a square matrix is required!\n");
        abort();
    }

    c->partition = flint_malloc(c->n * sizeof(slong));

    _fmpz_mat_get_sccs(c->partition, A);

    /* count the strongly connected components */
    c->k = 0;
    for (i = 0; i < c->n; i++)
    {
        u = c->partition[i];
        c->k = FLINT_MAX(c->k, u + 1);
    }

    /*
     * Compute the adjacency matrix of the condensation.
     * This should be strict lower triangular, so that visiting the
     * vertices in increasing order corresponds to a postorder traversal.
     */
    fmpz_mat_init(c->C, c->k, c->k);
    fmpz_mat_zero(c->C);
    for (i = 0; i < c->n; i++)
    {
        for (j = 0; j < c->n; j++)
        {
            if (!fmpz_is_zero(fmpz_mat_entry(A, i, j)))
            {
                u = c->partition[i];
                v = c->partition[j];
                if (u != v)
                {
                    fmpz_one(fmpz_mat_entry(c->C, u, v));
                }
            }
        }
    }

    if (!_fmpz_mat_is_strict_lower_triangular(c->C))
    {
        flint_printf("condensation_init: unexpected matrix structure\n");
        fmpz_mat_print_pretty(c->C);
        abort();
    }
}

void
condensation_clear(condensation_t c)
{
    fmpz_mat_clear(c->C);
    flint_free(c->partition);
}





typedef struct
{
    condensation_t con;
    fmpz_mat_t T; /* transitive closure of condensation */
    fmpz_mat_t P; /* is there a cycle in any component on a path from u to v */
    fmpz_mat_t Q; /* longest path, if any, from u to v */
    int *scc_has_cycle;
} connectivity_struct;
typedef connectivity_struct connectivity_t[1];

void
connectivity_fprint(FILE * file, connectivity_t c)
{
    slong i;
    flint_fprintf(file, "begin condensation ...\n");
    condensation_fprint(file, c->con);
    flint_fprintf(file, "... end condensation\n");
    flint_fprintf(file, "transitive closure of condensation:\n");
    fmpz_mat_fprint_pretty(file, c->T);
    flint_fprintf(file, "a path goes through a cycle-containing SCC:\n");
    fmpz_mat_fprint_pretty(file, c->P);
    flint_fprintf(file, "max path length in condensation:\n");
    fmpz_mat_fprint_pretty(file, c->Q);
    flint_fprintf(file, "SCC has cycle:\n");
    for (i = 0; i < c->con->k; i++)
    {
        flint_fprintf(file, "%wd : %d\n", i, c->scc_has_cycle[i]);
    }
}

void
connectivity_clear(connectivity_t c)
{
    fmpz_mat_clear(c->T);
    fmpz_mat_clear(c->P);
    fmpz_mat_clear(c->Q);
    flint_free(c->scc_has_cycle);
    condensation_clear(c->con);
}

void
_connectivity_init_scc_has_cycle(connectivity_t c, fmpz_mat_t A)
{
    slong n, i, u;
    slong *scc_size;

    n = fmpz_mat_nrows(A);
    c->scc_has_cycle = flint_calloc(n, sizeof(int));

    /*
     * If a vertex of the original graph has a loop,
     * then the strongly connected component to which it belongs has a cycle.
     */
    for (i = 0; i < n; i++)
    {
        if (!fmpz_is_zero(fmpz_mat_entry(A, i, i)))
        {
            u = c->con->partition[i];
            c->scc_has_cycle[u] = 1;
        }
    }

    /*
     * If a strongly connected component contains more than one vertex,
     * then that component has a cycle.
     */
    scc_size = flint_calloc(c->con->k, sizeof(slong));
    for (i = 0; i < n; i++)
    {
        u = c->con->partition[i];
        scc_size[u]++;
    }
    for (u = 0; u < c->con->k; u++)
    {
        if (scc_size[u] > 1)
        {
            c->scc_has_cycle[u] = 1;
        }
    }
    flint_free(scc_size);
}

void
connectivity_init(connectivity_t c, fmpz_mat_t A)
{
    slong u, v, w;
    slong k;
    slong curr, rest;

    /* compute the condensation */
    condensation_init(c->con, A);
    k = c->con->k;

    /* check whether each scc contains a cycle */
    _connectivity_init_scc_has_cycle(c, A);

    /* compute the transitive closure of the condensation */
    fmpz_mat_init(c->T, k, k);
    _fmpz_mat_transitive_closure(c->T, c->con->C);

    /*
     * Is there a walk from u to v that passes through a cycle-containing scc?
     * Cycles in the components u and v themselves are not considered.
     * Remember that the condensation is a directed acyclic graph.
     */
    fmpz_mat_init(c->P, k, k);
    fmpz_mat_zero(c->P);
    for (w = 0; w < k; w++)
    {
        if (c->scc_has_cycle[w])
        {
            for (u = 0; u < k; u++)
            {
                for (v = 0; v < k; v++)
                {
                    if (!fmpz_is_zero(fmpz_mat_entry(c->T, u, w)) &&
                        !fmpz_is_zero(fmpz_mat_entry(c->T, w, v)))
                    {
                        fmpz_one(fmpz_mat_entry(c->P, u, v));
                    }
                }
            }
        }
    }

    /*
     * What is the max length path from u to v in the condensation graph?
     * If u==v or if v is unreachable from u then let this be zero.
     * Remember that the condensation is a directed acyclic graph,
     * and that the components are indexed in a post-order traversal.
     */
    fmpz_mat_init(c->Q, k, k);
    fmpz_mat_zero(c->Q);
    for (u = 0; u < k; u++)
    {
        for (w = 0; w < k; w++)
        {
            if (!fmpz_is_zero(fmpz_mat_entry(c->con->C, u, w)))
            {
                curr = fmpz_get_si(fmpz_mat_entry(c->Q, u, w));
                fmpz_set_si(
                        fmpz_mat_entry(c->Q, u, w),
                        FLINT_MAX(curr, 1));
                for (v = 0; v < k; v++)
                {
                    if (!fmpz_is_zero(fmpz_mat_entry(c->T, w, v)))
                    {
                        rest = fmpz_get_si(fmpz_mat_entry(c->Q, w, v));
                        curr = fmpz_get_si(fmpz_mat_entry(c->Q, u, v));
                        fmpz_set_si(
                                fmpz_mat_entry(c->Q, u, v),
                                FLINT_MAX(curr, rest + 1));
                    }
                }
            }
        }
    }
}


void
connectivity_init_arb_mat(connectivity_t c, const arb_mat_t A)
{
    slong i, j, dim;
    fmpz_mat_t B;

    dim = arb_mat_nrows(A);
    fmpz_mat_init(B, dim, dim);
    fmpz_mat_zero(B);

    for (i = 0; i < dim; i++)
    {
        for (j = 0; j < dim; j++)
        {
            if (!arb_is_zero(arb_mat_entry(A, i, j)))
            {
                fmpz_one(fmpz_mat_entry(B, i, j));
            }
        }
    }

    connectivity_init(c, B);

    fmpz_mat_clear(B);
}

void
connectivity_sufficient_N(arb_t N, connectivity_t c, slong i, slong j)
{
    slong u, v;
    u = c->con->partition[i];
    v = c->con->partition[j];
    if (u == v)
    {
        if (c->scc_has_cycle[u])
        {
            arb_pos_inf(N);
        }
        else
        {
            arb_one(N);
        }
    }
    else if (fmpz_is_zero(fmpz_mat_entry(c->T, u, v)))
    {
        arb_one(N);
    }
    else if (
            c->scc_has_cycle[u] ||
            c->scc_has_cycle[v] ||
            !fmpz_is_zero(fmpz_mat_entry(c->P, u, v)))
    {
        arb_pos_inf(N);
    }
    else
    {
        fmpz_t n;
        fmpz_init(n);
        fmpz_add_ui(n, fmpz_mat_entry(c->Q, u, v), 1);
        arb_set_fmpz(N, n);
        fmpz_clear(n);
    }
}


void
_arb_mat_exp_sufficient_N(arb_mat_t M, const arb_mat_t A)
{
    slong i, j;
    connectivity_t c;
    connectivity_init_arb_mat(c, A);
    for (i = 0; i < c->con->n; i++)
    {
        for (j = 0; j < c->con->n; j++)
        {
            connectivity_sufficient_N(arb_mat_entry(M, i, j), c, i, j);
        }
    }
    connectivity_clear(c);
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
    _fmpz_mat_transitive_closure(C, C);
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
        int using_structure = 0;

        arb_mat_t C;
        int using_connectivity = 0;

        if (1)
            using_connectivity = _arb_mat_any_is_zero(A);
        if (using_connectivity)
        {
            arb_mat_init(C, dim, dim);
            _arb_mat_exp_sufficient_N(C, A);
        }

        if (0)
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

        /* if A is structurally nilpotent then set N to its degree */
        if (using_connectivity)
        {
            arb_t n;
            arb_init(n);
            _arb_mat_max_exact(n, C);
            if (_arb_lt_si(n, N))
                N = arf_get_si(arb_midref(n), ARF_RND_UP);
            arb_clear(n);
        }

        mag_exp_tail(err, norm, N);

        _arb_mat_exp_taylor(B, T, N, wp);

        if (using_connectivity)
        {
            for (i = 0; i < dim; i++)
                for (j = 0; j < dim; j++)
                    if (_arb_gt_si(arb_mat_entry(C, i, j), N))
                        arb_add_error_mag(arb_mat_entry(B, i, j), err);
            arb_mat_clear(C);
        }
        else
        {
            for (i = 0; i < dim; i++)
                for (j = 0; j < dim; j++)
                    arb_add_error_mag(arb_mat_entry(B, i, j), err);
        }

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

