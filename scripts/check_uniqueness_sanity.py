#!/usr/bin/env python3
"""Deterministic numerical sanity checks for the uniqueness extension.

These checks use only floating-point arithmetic and deterministic quadrature. They are external
diagnostics, not proof dependencies; the trusted Lean development does not use their results.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import erfc, exp, fsum, isfinite, pi, sqrt
from random import Random
from typing import Callable, Sequence


Matrix = tuple[tuple[float, ...], ...]

RADIUS_SEED = 20_260_719
RECTANGLE_CASES = 5
CORRELATED_RHO = 0.5
SINGULAR_RHO = 1.0
QUADRATURE_FINE_SUBINTERVALS = 4096
QUADRATURE_COARSE_SUBINTERVALS = QUADRATURE_FINE_SUBINTERVALS // 2
QUADRATURE_CONVERGENCE_TOLERANCE = 5e-12
STRICT_GAP_TOLERANCE = 1e-6
EQUALITY_TOLERANCE = 5e-13
PSD_TOLERANCE = 1e-12
LOWER_TAIL_CUTOFF = -9.0


@dataclass(frozen=True)
class SanityResult:
    """One diagnostic result and enough detail to reproduce its decision."""

    name: str
    passed: bool
    detail: str


def standard_normal_cdf(x: float) -> float:
    """Standard-normal CDF, retaining accuracy in the negative tail."""
    return 0.5 * erfc(-x / sqrt(2.0))


def standard_normal_density(x: float) -> float:
    """Standard-normal density."""
    return exp(-(x * x) / 2.0) / sqrt(2.0 * pi)


def composite_simpson(
    function: Callable[[float], float],
    lower: float,
    upper: float,
    subintervals: int,
) -> float:
    """Integrate on a finite interval by fixed-grid composite Simpson quadrature."""
    if subintervals <= 0 or subintervals % 2:
        raise ValueError("subintervals must be a positive even integer")
    if not isfinite(lower) or not isfinite(upper):
        raise ValueError("quadrature endpoints must be finite")
    if lower == upper:
        return 0.0

    step = (upper - lower) / subintervals
    odd_sum = fsum(
        function(lower + index * step) for index in range(1, subintervals, 2)
    )
    even_sum = fsum(
        function(lower + index * step) for index in range(2, subintervals, 2)
    )
    return (step / 3.0) * (
        function(lower) + function(upper) + 4.0 * odd_sum + 2.0 * even_sum
    )


def _validate_admissible_bivariate_rho(rho: float) -> None:
    if not 0.0 <= rho <= 1.0:
        raise ValueError("an admissible bivariate equicorrelation requires 0 <= rho <= 1")


def symmetric_rectangle_probability(
    first_radius: float,
    second_radius: float,
    rho: float,
    subintervals: int = QUADRATURE_FINE_SUBINTERVALS,
) -> float:
    """Probability of a centered bivariate Gaussian symmetric rectangle."""
    if first_radius < 0.0 or second_radius < 0.0:
        raise ValueError("rectangle radii must be nonnegative")
    _validate_admissible_bivariate_rho(rho)

    first_mass = 2.0 * standard_normal_cdf(first_radius) - 1.0
    second_mass = 2.0 * standard_normal_cdf(second_radius) - 1.0
    if rho == 0.0:
        return first_mass * second_mass
    if rho == 1.0:
        radius = min(first_radius, second_radius)
        return 2.0 * standard_normal_cdf(radius) - 1.0

    conditional_sd = sqrt(1.0 - rho * rho)

    def integrand(x: float) -> float:
        conditional_mass = standard_normal_cdf(
            (second_radius - rho * x) / conditional_sd
        ) - standard_normal_cdf((-second_radius - rho * x) / conditional_sd)
        return standard_normal_density(x) * conditional_mass

    return composite_simpson(integrand, -first_radius, first_radius, subintervals)


def equal_lower_orthant_probability(
    threshold: float,
    rho: float,
    subintervals: int = QUADRATURE_FINE_SUBINTERVALS,
) -> float:
    """Probability that both bivariate Gaussian coordinates are at most ``threshold``."""
    _validate_admissible_bivariate_rho(rho)
    marginal_mass = standard_normal_cdf(threshold)
    if rho == 0.0:
        return marginal_mass * marginal_mass
    if rho == 1.0:
        return marginal_mass
    if threshold <= LOWER_TAIL_CUTOFF:
        raise ValueError("threshold must exceed the fixed lower-tail cutoff")

    conditional_sd = sqrt(1.0 - rho * rho)

    def integrand(x: float) -> float:
        conditional_mass = standard_normal_cdf((threshold - rho * x) / conditional_sd)
        return standard_normal_density(x) * conditional_mass

    return composite_simpson(
        integrand,
        LOWER_TAIL_CUTOFF,
        threshold,
        subintervals,
    )


def bivariate_coordinate_max_mgf(mu: float, rho: float) -> float:
    """Closed-form MGF of the maximum of two centered unit Gaussians."""
    if not -1.0 <= rho <= 1.0:
        raise ValueError("rho must be a correlation in [-1, 1]")
    folded_scale = sqrt((1.0 - rho) / 2.0)
    return 2.0 * exp(mu * mu / 2.0) * standard_normal_cdf(mu * folded_scale)


def bivariate_coordinate_max_mgf_quadrature(
    mu: float,
    rho: float,
    subintervals: int = QUADRATURE_FINE_SUBINTERVALS,
) -> float:
    """Integrate the bivariate maximum density after completing the square."""
    if not -1.0 < rho <= 1.0:
        raise ValueError("density quadrature requires a correlation in (-1, 1]")
    density_scale = sqrt((1.0 - rho) / (1.0 + rho))
    exponential_factor = 2.0 * exp(mu * mu / 2.0)

    def shifted_integrand(z: float) -> float:
        return standard_normal_density(z) * standard_normal_cdf(
            (z + mu) * density_scale
        )

    return exponential_factor * composite_simpson(
        shifted_integrand,
        LOWER_TAIL_CUTOFF,
        -LOWER_TAIL_CUTOFF,
        subintervals,
    )


def identity_matrix(size: int) -> Matrix:
    if size <= 0:
        raise ValueError("matrix size must be positive")
    return tuple(
        tuple(1.0 if row == column else 0.0 for column in range(size))
        for row in range(size)
    )


def equicorrelation_matrix(size: int, rho: float) -> Matrix:
    if size <= 1:
        raise ValueError("equicorrelation checks require size at least two")
    return tuple(
        tuple(1.0 if row == column else rho for column in range(size))
        for row in range(size)
    )


def equicorrelation_eigenvalues(size: int, rho: float) -> tuple[float, ...]:
    """Analytic spectrum of the equicorrelation matrix."""
    if size <= 1:
        raise ValueError("equicorrelation checks require size at least two")
    return (1.0 + (size - 1) * rho,) + (1.0 - rho,) * (size - 1)


def weak_simplex_residual_eigenvalues(size: int, rho: float) -> tuple[float, ...]:
    """Spectrum of ``R - J / size`` for equicorrelation ``R``."""
    if size <= 1:
        raise ValueError("equicorrelation checks require size at least two")
    return ((size - 1) * rho,) + (1.0 - rho,) * (size - 1)


def regular_simplex_gram(size: int) -> Matrix:
    if size <= 1:
        raise ValueError("a regular-simplex Gram matrix requires size at least two")
    off_diagonal = -1.0 / (size - 1)
    return equicorrelation_matrix(size, off_diagonal)


def normalized_gram_covariance(gram: Matrix) -> Matrix:
    size = _validate_square_matrix(gram)
    if size <= 1:
        raise ValueError("Gram normalization requires size at least two")
    alpha = (size - 1.0) / size
    common = 1.0 / size
    return tuple(
        tuple(alpha * gram[row][column] + common for column in range(size))
        for row in range(size)
    )


def matrix_max_abs_difference(first: Matrix, second: Matrix) -> float:
    size = _validate_square_matrix(first)
    if _validate_square_matrix(second) != size:
        raise ValueError("matrices must have the same dimensions")
    return max(
        abs(first[row][column] - second[row][column])
        for row in range(size)
        for column in range(size)
    )


def bayes_value_at_zero(gram: Matrix) -> float:
    """Bayes value at zero signal; every class likelihood is identically one."""
    class_count = _validate_square_matrix(gram)
    return 1.0 / class_count


def _validate_square_matrix(matrix: Matrix) -> int:
    size = len(matrix)
    if size == 0 or any(len(row) != size for row in matrix):
        raise ValueError("matrix must be nonempty and square")
    return size


def seeded_rectangle_radii() -> tuple[tuple[float, float], ...]:
    """Fixed-seed positive radii; randomness selects inputs, not probability estimates."""
    generator = Random(RADIUS_SEED)
    return tuple(
        (
            round(generator.uniform(0.35, 1.75), 6),
            round(generator.uniform(0.35, 1.75), 6),
        )
        for _ in range(RECTANGLE_CASES)
    )


def _strict_result(name: str, correlated: float, independent: float, error: float) -> SanityResult:
    gap = correlated - independent
    passed = gap > STRICT_GAP_TOLERANCE and error <= QUADRATURE_CONVERGENCE_TOLERANCE
    return SanityResult(
        name,
        passed,
        f"correlated={correlated:.15g}, independent={independent:.15g}, "
        f"gap={gap:.3e}, coarse/fine={error:.3e}",
    )


def run_sanity_checks() -> list[SanityResult]:
    """Run the complete deterministic diagnostic suite."""
    results: list[SanityResult] = []

    singular_covariance_eigenvalues = equicorrelation_eigenvalues(2, SINGULAR_RHO)
    singular_residual_eigenvalues = weak_simplex_residual_eigenvalues(2, SINGULAR_RHO)
    singular_admissible = (
        min(singular_covariance_eigenvalues) >= -PSD_TOLERANCE
        and min(singular_residual_eigenvalues) >= -PSD_TOLERANCE
        and min(abs(value) for value in singular_covariance_eigenvalues) <= PSD_TOLERANCE
    )
    results.append(
        SanityResult(
            "singular admissible all-ones covariance",
            singular_admissible,
            f"covariance spectrum={singular_covariance_eigenvalues}, "
            f"residual spectrum={singular_residual_eigenvalues}",
        )
    )

    pd_covariance_eigenvalues = equicorrelation_eigenvalues(2, CORRELATED_RHO)
    pd_residual_eigenvalues = weak_simplex_residual_eigenvalues(2, CORRELATED_RHO)
    pd_admissible = (
        min(pd_covariance_eigenvalues) > PSD_TOLERANCE
        and min(pd_residual_eigenvalues) >= -PSD_TOLERANCE
        and CORRELATED_RHO > EQUALITY_TOLERANCE
    )
    results.append(
        SanityResult(
            "nonidentity positive-definite admissible covariance",
            pd_admissible,
            f"rho={CORRELATED_RHO}, covariance spectrum={pd_covariance_eigenvalues}, "
            f"residual spectrum={pd_residual_eigenvalues}",
        )
    )

    for first_radius, second_radius in seeded_rectangle_radii():
        fine = symmetric_rectangle_probability(
            first_radius,
            second_radius,
            CORRELATED_RHO,
            QUADRATURE_FINE_SUBINTERVALS,
        )
        coarse = symmetric_rectangle_probability(
            first_radius,
            second_radius,
            CORRELATED_RHO,
            QUADRATURE_COARSE_SUBINTERVALS,
        )
        independent = (
            (2.0 * standard_normal_cdf(first_radius) - 1.0)
            * (2.0 * standard_normal_cdf(second_radius) - 1.0)
        )
        results.append(
            _strict_result(
                f"strict rectangle radii=({first_radius:.6f}, {second_radius:.6f})",
                fine,
                independent,
                abs(fine - coarse),
            )
        )

    for threshold in (-1.0, 0.0, 1.0):
        fine = equal_lower_orthant_probability(
            threshold,
            CORRELATED_RHO,
            QUADRATURE_FINE_SUBINTERVALS,
        )
        coarse = equal_lower_orthant_probability(
            threshold,
            CORRELATED_RHO,
            QUADRATURE_COARSE_SUBINTERVALS,
        )
        independent = standard_normal_cdf(threshold) ** 2
        results.append(
            _strict_result(
                f"strict lower orthant threshold={threshold:+.1f}",
                fine,
                independent,
                abs(fine - coarse),
            )
        )

    for mu in (0.1, 0.35, 0.75, 1.5, 2.0):
        correlated = bivariate_coordinate_max_mgf_quadrature(
            mu,
            CORRELATED_RHO,
            QUADRATURE_FINE_SUBINTERVALS,
        )
        correlated_coarse = bivariate_coordinate_max_mgf_quadrature(
            mu,
            CORRELATED_RHO,
            QUADRATURE_COARSE_SUBINTERVALS,
        )
        independent = bivariate_coordinate_max_mgf_quadrature(
            mu,
            0.0,
            QUADRATURE_FINE_SUBINTERVALS,
        )
        independent_coarse = bivariate_coordinate_max_mgf_quadrature(
            mu,
            0.0,
            QUADRATURE_COARSE_SUBINTERVALS,
        )
        gap = independent - correlated
        convergence_error = max(
            abs(correlated - correlated_coarse),
            abs(independent - independent_coarse),
        )
        closed_form_error = max(
            abs(correlated - bivariate_coordinate_max_mgf(mu, CORRELATED_RHO)),
            abs(independent - bivariate_coordinate_max_mgf(mu, 0.0)),
        )
        results.append(
            SanityResult(
                f"strict coordinate-max MGF mu={mu:g}",
                gap > STRICT_GAP_TOLERANCE
                and convergence_error <= QUADRATURE_CONVERGENCE_TOLERANCE
                and closed_form_error <= EQUALITY_TOLERANCE,
                f"correlated={correlated:.15g}, independent={independent:.15g}, "
                f"independent-correlated={gap:.3e}, coarse/fine={convergence_error:.3e}, "
                f"closed-form error={closed_form_error:.3e}",
            )
        )

    identity_errors: list[float] = []
    identity_radius = seeded_rectangle_radii()[0]
    identity_errors.append(
        abs(
            symmetric_rectangle_probability(*identity_radius, 0.0)
            - (2.0 * standard_normal_cdf(identity_radius[0]) - 1.0)
            * (2.0 * standard_normal_cdf(identity_radius[1]) - 1.0)
        )
    )
    identity_errors.extend(
        abs(
            equal_lower_orthant_probability(threshold, 0.0)
            - standard_normal_cdf(threshold) ** 2
        )
        for threshold in (-1.0, 0.0, 1.0)
    )
    identity_errors.extend(
        abs(
            bivariate_coordinate_max_mgf_quadrature(mu, 0.0)
            - bivariate_coordinate_max_mgf(mu, 0.0)
        )
        for mu in (0.1, 0.75, 2.0)
    )
    identity_error = max(identity_errors)
    results.append(
        SanityResult(
            "equality at identity covariance",
            identity_error <= EQUALITY_TOLERANCE,
            f"maximum equality error={identity_error:.3e}",
        )
    )

    simplex_gram = regular_simplex_gram(2)
    normalized_simplex = normalized_gram_covariance(simplex_gram)
    normalization_error = matrix_max_abs_difference(normalized_simplex, identity_matrix(2))
    gram_identity_errors = []
    alpha = 0.5
    for lam in (0.25, 0.8, 1.4):
        left = exp(-lam * lam / 2.0) * bivariate_coordinate_max_mgf(lam, -1.0)
        normalized_lam = lam / sqrt(alpha)
        right = exp(-normalized_lam * normalized_lam / 2.0) * (
            bivariate_coordinate_max_mgf(normalized_lam, 0.0)
        )
        gram_identity_errors.append(abs(left - right))
    gram_identity_error = max(gram_identity_errors)
    results.append(
        SanityResult(
            "equality at regular-simplex Gram normalization",
            max(normalization_error, gram_identity_error) <= EQUALITY_TOLERANCE,
            f"matrix error={normalization_error:.3e}, "
            f"prefactored-MGF error={gram_identity_error:.3e}",
        )
    )

    nonsimplex_gram = equicorrelation_matrix(2, 1.0)
    gram_separation = matrix_max_abs_difference(nonsimplex_gram, simplex_gram)
    nonsimplex_zero_value = bayes_value_at_zero(nonsimplex_gram)
    simplex_zero_value = bayes_value_at_zero(simplex_gram)
    zero_value_error = abs(nonsimplex_zero_value - simplex_zero_value)
    results.append(
        SanityResult(
            "Bayes non-uniqueness at lambda=0",
            gram_separation > STRICT_GAP_TOLERANCE
            and zero_value_error <= EQUALITY_TOLERANCE,
            f"Gram separation={gram_separation:.3e}, values=({nonsimplex_zero_value:.15g}, "
            f"{simplex_zero_value:.15g}), equality error={zero_value_error:.3e}",
        )
    )

    return results


def exit_code(results: Sequence[SanityResult]) -> int:
    """Return zero exactly when every diagnostic passed."""
    return 0 if results and all(result.passed for result in results) else 1


def main() -> int:
    results = run_sanity_checks()
    print("Deterministic numerical diagnostics only; these are not proof dependencies.")
    print(
        "Quadrature: composite Simpson "
        f"{QUADRATURE_COARSE_SUBINTERVALS}/{QUADRATURE_FINE_SUBINTERVALS}; "
        f"convergence tolerance={QUADRATURE_CONVERGENCE_TOLERANCE:.1e}; "
        f"strict-gap tolerance={STRICT_GAP_TOLERANCE:.1e}; "
        f"equality tolerance={EQUALITY_TOLERANCE:.1e}."
    )
    for result in results:
        status = "PASS" if result.passed else "FAIL"
        print(f"{status}: {result.name}: {result.detail}")
    passed = sum(result.passed for result in results)
    print(f"Summary: {passed}/{len(results)} checks passed.")
    return exit_code(results)


if __name__ == "__main__":
    raise SystemExit(main())
