import subprocess
import sys
from pathlib import Path
from unittest import TestCase, main

from check_uniqueness_sanity import (
    EQUALITY_TOLERANCE,
    SanityResult,
    bayes_value_at_zero,
    bivariate_coordinate_max_mgf,
    bivariate_coordinate_max_mgf_quadrature,
    composite_simpson,
    equal_lower_orthant_probability,
    equicorrelation_matrix,
    exit_code,
    identity_matrix,
    matrix_max_abs_difference,
    normalized_gram_covariance,
    regular_simplex_gram,
    run_sanity_checks,
    seeded_rectangle_radii,
    standard_normal_cdf,
    symmetric_rectangle_probability,
)


class NumericalPrimitiveTests(TestCase):
    def test_normal_cdf_and_simpson_polynomial(self) -> None:
        self.assertEqual(standard_normal_cdf(0.0), 0.5)
        self.assertAlmostEqual(composite_simpson(lambda x: x**3, 0.0, 1.0, 20), 0.25)

    def test_seeded_radii_are_stable_and_positive(self) -> None:
        self.assertEqual(
            seeded_rectangle_radii(),
            (
                (1.687982, 1.123531),
                (1.682162, 0.585699),
                (1.375709, 0.857278),
                (0.936116, 1.712822),
                (0.553056, 0.755298),
            ),
        )
        self.assertTrue(all(a > 0.0 and b > 0.0 for a, b in seeded_rectangle_radii()))

    def test_identity_and_singular_probability_endpoints(self) -> None:
        first_radius, second_radius = 0.8, 1.3
        independent_rectangle = (
            (2.0 * standard_normal_cdf(first_radius) - 1.0)
            * (2.0 * standard_normal_cdf(second_radius) - 1.0)
        )
        self.assertEqual(
            symmetric_rectangle_probability(first_radius, second_radius, 0.0),
            independent_rectangle,
        )
        self.assertEqual(
            symmetric_rectangle_probability(first_radius, second_radius, 1.0),
            2.0 * standard_normal_cdf(first_radius) - 1.0,
        )
        for threshold in (-1.0, 0.0, 1.0):
            marginal = standard_normal_cdf(threshold)
            self.assertEqual(equal_lower_orthant_probability(threshold, 0.0), marginal**2)
            self.assertEqual(equal_lower_orthant_probability(threshold, 1.0), marginal)

    def test_closed_max_mgf_endpoints_and_strict_case(self) -> None:
        for rho in (-1.0, 0.0, 0.5, 1.0):
            self.assertAlmostEqual(bivariate_coordinate_max_mgf(0.0, rho), 1.0)
        for mu in (0.1, 0.75, 2.0):
            self.assertLess(
                bivariate_coordinate_max_mgf(mu, 0.5),
                bivariate_coordinate_max_mgf(mu, 0.0),
            )
            self.assertAlmostEqual(
                bivariate_coordinate_max_mgf_quadrature(mu, 0.5),
                bivariate_coordinate_max_mgf(mu, 0.5),
                places=12,
            )

    def test_regular_simplex_normalizes_to_identity(self) -> None:
        for size in (2, 3, 5):
            normalized = normalized_gram_covariance(regular_simplex_gram(size))
            self.assertLessEqual(
                matrix_max_abs_difference(normalized, identity_matrix(size)),
                EQUALITY_TOLERANCE,
            )

    def test_zero_signal_bayes_value_does_not_determine_gram(self) -> None:
        simplex = regular_simplex_gram(2)
        nonsimplex = equicorrelation_matrix(2, 1.0)
        self.assertGreater(matrix_max_abs_difference(simplex, nonsimplex), 1.0)
        self.assertEqual(bayes_value_at_zero(simplex), bayes_value_at_zero(nonsimplex))
        self.assertEqual(bayes_value_at_zero(simplex), 0.5)

    def test_invalid_inputs_are_rejected(self) -> None:
        with self.assertRaises(ValueError):
            composite_simpson(lambda x: x, 0.0, 1.0, 3)
        with self.assertRaises(ValueError):
            symmetric_rectangle_probability(1.0, 1.0, -0.1)
        with self.assertRaises(ValueError):
            equal_lower_orthant_probability(-10.0, 0.5)
        with self.assertRaises(ValueError):
            bivariate_coordinate_max_mgf(1.0, 1.1)


class SanitySuiteTests(TestCase):
    def test_complete_suite_passes(self) -> None:
        results = run_sanity_checks()
        self.assertEqual(len(results), 18)
        self.assertEqual([result.name for result in results if not result.passed], [])
        self.assertEqual(exit_code(results), 0)

    def test_exit_code_rejects_empty_or_failing_results(self) -> None:
        self.assertEqual(exit_code([]), 1)
        self.assertEqual(exit_code([SanityResult("failure", False, "expected")]), 1)

    def test_script_runs_standalone(self) -> None:
        script = Path(__file__).with_name("check_uniqueness_sanity.py")
        completed = subprocess.run(
            [sys.executable, str(script)],
            check=False,
            capture_output=True,
            text=True,
            timeout=10,
        )
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertIn("not proof dependencies", completed.stdout)
        self.assertIn("Summary: 18/18 checks passed.", completed.stdout)


if __name__ == "__main__":
    main()
