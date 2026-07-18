# Principal theorem dependencies

This graph records the main public interfaces connecting the adaptive-tilting and centered-product branches to Gaussian stochastic domination and the coding theorem. It omits private implementation lemmas and routine measure-theoretic support.

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
