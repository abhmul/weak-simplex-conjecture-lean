# Principal theorem dependencies

This graph records the main public interfaces connecting the adaptive-tilting and centered-product branches to Gaussian stochastic domination and the coding theorem. It omits private implementation lemmas and routine measure-theoretic support.

## Non-strict chain

```text
rankOne_inverse_bound
  → exists_adaptivePotential_maximizer_with_value
  → exists_adaptiveWitnesses
exists_adaptiveWitnesses + Gaussian shift + centered tilted-half-line/event-shift identities
  → lowerOrthant_ge_iid_of_posDef_of_centeredProduct

prekopa_leindler + measurable_isLogConcave_lintegral_right
  → symmetricRectangle_ge_iid_of_posDef
  → even_logConcave_product_of_posDef
even_logConcave_product_of_posDef + Gaussian product-rotation invariance
  → normalizedSelfConvolution_product_deficit_of_posDef
normalizedSelfConvolution_law
  → hasLaw_iteratedNormalizedSelfConvolution_dyadicSum
  → tendstoInDistribution_iteratedNormalizedSelfConvolution
tendstoInDistribution_iteratedNormalizedSelfConvolution
  + exists_pos_le_gaussianDensityRatio_on_box
  → exists_eventual_pos_lower_bound_integral_iteratedNormalizedSelfConvolution
the product-deficit theorem + the eventual positive lower bound
  → centered_product_of_posDef

lowerOrthant_ge_iid_of_posDef_of_centeredProduct + centered_product_of_posDef
  → lowerOrthant_ge_iid_of_posDef
  → lowerOrthant_ge_iid
  → coordinateMax_tail_le_iid
  → gaussianMax_mgf_le_regularSimplex

gramNormalization + gramMgf_normalization_identity + gaussianMax_mgf_le_regularSimplex
  → gramGaussianMax_mgf_le_regularSimplex
map_codeScore_stdGaussian + bayesValue_eq_gramMgf
  + gramGaussianMax_mgf_le_regularSimplex
  → bayesValue_le_regularSimplex
measurable maximizing decoder + finite tie partition
  → decoderSuccessOf_eq_bayesValue
bayesValue_le_regularSimplex + mlDecoder_success_eq_bayesValue
  → weak_simplex
bayesValue_le_regularSimplex + decoderSuccessOf_eq_bayesValue
  → weak_simplex_of_scoreMaximizingDecoders
```

## Rigidity and uniqueness chain

```text
regularizedCovariance + centered_product_of_posDef
  → centered_product_of_continuous
symmetricRectangle_ge_iid + symmetricRectangle_gt_iid_of_ne_one
  + H_pos
  + normalizedCenteredTiltedHalfLine_product
  + continuous_normalizedSelfConvolution_normalizedCenteredTiltedHalfLine
  + centered_product_of_continuous
  + integral_integral_sumDifferenceProduct_eq_sq
  + lowerOrthant_ge_iid
  → centeredTiltedHalfLine_product_lt_of_ne_one

regularizedCovariance + exists_adaptiveWitnesses
  + compact witness bounds and continuity
  → exists_adaptiveWitnesses_of_weakSimplexCov
exists_adaptiveWitnesses_of_weakSimplexCov
  + adaptiveValue_exp_bound
  + adaptiveProduct_mass_eq
  + lowerOrthant_eq_adaptiveProduct
  + centeredTiltedHalfLine_product_lt_of_ne_one
  → lowerOrthant_gt_iid_of_ne_one
  → lowerOrthant_eq_iid_iff

lowerOrthant_gt_iid_of_ne_one
  → coordinateMax_tail_lt_iid_of_ne_one
coordinateMax_tail_le_iid + coordinateMax_tail_lt_iid_of_ne_one
  + exponential-transform integrability
  → gaussianMax_mgf_lt_regularSimplex
  → gaussianMax_mgf_eq_regularSimplex_iff

gramNormalization_eq_one_iff
  + gramMgf_normalization_identity
  + gaussianMax_mgf_lt_regularSimplex
  → gramGaussianMax_mgf_lt_regularSimplex
  → gramGaussianMax_mgf_eq_regularSimplex_iff
gramGaussianMax_mgf_lt_regularSimplex + bayesValue_eq_gramMgf
  → bayesValue_lt_regularSimplex
gramGaussianMax_mgf_eq_regularSimplex_iff + bayesValue_eq_gramMgf
  → bayesValue_eq_regularSimplex_iff

bayesValue_lt_regularSimplex + mlDecoder_success_eq_bayesValue
  → weak_simplex_strict
bayesValue_eq_regularSimplex_iff + mlDecoder_success_eq_bayesValue
  → weak_simplex_eq_iff_codeGram_eq
bayesValue_lt_regularSimplex
  + IsScoreMaximizingDecoder.isLikelihoodMaximizing
  + decoderSuccessOf_eq_bayesValue
  → weak_simplex_strict_of_scoreMaximizingDecoders
bayesValue_eq_regularSimplex_iff
  + IsScoreMaximizingDecoder.isLikelihoodMaximizing
  + decoderSuccessOf_eq_bayesValue
  → weak_simplex_eq_iff_codeGram_eq_of_scoreMaximizingDecoders
```

Every strict or equality-characterization theorem in the coding layer assumes `lam > 0`; the existing non-strict theorems retain their `0 ≤ lam` range. The certified uniqueness invariant is `codeGram code = regularSimplexGram`; orthogonal congruence of realizations is an optional downstream theorem.

The general theorem `centered_product_of_posDef` remains positive-definite. The rigidity branch has two isolated singular-covariance exceptions: a non-strict continuous-factor limit, used to derive the specialized strict adaptive-half-line product theorem, and a compact-limit constructor for adaptive witnesses. No generic singular centered-product strictness or equality characterization is asserted.
