import Flagship1D.Solution

/-! Axiom audit and statement check: each `example` re-checks that the proved theorem has
exactly the Challenge statement as its type. -/

namespace Flagship1D

example : SparseInheritedBySubsets := sparseInheritedBySubsets
example : SparseImpliesNextSparse := sparseImpliesNextSparse
example : FullBoxNotSparse := fullBoxNotSparse
example : Lemma_4_2_Witness := lemma_4_2_witness
example : Lemma_4_2_PairCount := lemma_4_2_pairCount
example : BjRecursion := bjRecursion
example : IndependentSelection := independentSelection
example : ProductOnDisjointSupports := productOnDisjointSupports
example : TreeBound := treeBound
example : Num_CavityGain := num_cavityGain
example : Num_FlankPass := num_flankPass
example : Num_FlankResponseTime := num_flankResponseTime
example : Num_ClearanceTime := num_clearanceTime
example : Num_ResponseTime := num_responseTime
example : Num_CavityLength := num_cavityLength
example : Num_WoundBand := num_woundBand
example : Num_SeedRatio := num_seedRatio
example : Num_SeedSpacing := num_seedSpacing
example : Num_SeedCount := num_seedCount
example : Num_EpochCost := num_epochCost
example : Num_TransportMargin := num_transportMargin
example : Num_RearWall := num_rearWall
example : Num_OwnerCollar := num_ownerCollar
example : Num_CommonSpan := num_commonSpan
example : Num_SatelliteWidth := num_satelliteWidth
example : Num_DeficitConstant := num_deficitConstant
example : Num_Recruitment := num_recruitment
example : Num_AdvanceDebit := num_advanceDebit
example : Num_EndpointException := num_endpointException
example : Num_EndGap := num_endGap
example : Num_FullBoxHypothesis := num_fullBoxHypothesis
example : RestrictedWitnessTrees := restrictedWitnessTrees
example : WitnessTreeShape := witnessTreeShape
example : WitnessTreeCount := witnessTreeCount
example : MeshRootCover := meshRootCover
example : ConflictDegreeArea := conflictDegreeArea
example : WitnessTreeProbability := witnessTreeProbability
example : Q1_L1 := q1_l1
example : Q1_L1_Threshold := q1_l1_threshold
example : Lemma_4_2_Probability := lemma_4_2_probability
example : LeafOverlapDegree := leafOverlapDegree
example : ExponentBookkeeping := exponentBookkeeping
example : NestedTestSumRaw := nestedTestSumRaw

#print axioms sparseInheritedBySubsets
#print axioms sparseImpliesNextSparse
#print axioms fullBoxNotSparse
#print axioms lemma_4_2_witness
#print axioms lemma_4_2_pairCount
#print axioms bjRecursion
#print axioms independentSelection
#print axioms productOnDisjointSupports
#print axioms treeBound
#print axioms num_cavityGain
#print axioms num_flankPass
#print axioms num_flankResponseTime
#print axioms num_clearanceTime
#print axioms num_responseTime
#print axioms num_cavityLength
#print axioms num_woundBand
#print axioms num_seedRatio
#print axioms num_seedSpacing
#print axioms num_seedCount
#print axioms num_epochCost
#print axioms num_transportMargin
#print axioms num_rearWall
#print axioms num_ownerCollar
#print axioms num_commonSpan
#print axioms num_satelliteWidth
#print axioms num_deficitConstant
#print axioms num_recruitment
#print axioms num_advanceDebit
#print axioms num_endpointException
#print axioms num_endGap
#print axioms num_fullBoxHypothesis
#print axioms restrictedWitnessTrees
#print axioms witnessTreeShape
#print axioms witnessTreeCount
#print axioms meshRootCover
#print axioms conflictDegreeArea
#print axioms witnessTreeProbability
#print axioms q1_l1
#print axioms q1_l1_threshold
#print axioms lemma_4_2_probability
#print axioms leafOverlapDegree
#print axioms exponentBookkeeping
#print axioms nestedTestSumRaw


/-! Sprint-2 extension: Lemma 12.2 and the arithmetic of Lemma 16.1 of the quantum storage paper. -/
example : Q1_L1_1 := q1_l1_1
example : Q1_L1_1_Uniform := q1_l1_1_uniform
example : Q1_L18_Recursion := q1_l18_recursion
example : Q1_L18_Horizon := q1_l18_horizon
example : Q1_L18_Fidelity := q1_l18_fidelity
example : Q1_L18_K0 := q1_l18_k0
example : Q1_L18_FidelityAtTimes := q1_l18_fidelity_at_times
example : Q1_L12_Ledger := q1_l12_ledger
example : Q1_L12_Step1 := q1_l12_step1
example : Q1_L11_Ledger := q1_l11_ledger
example : Q1_L18_RankExists := q1_l18_rank_exists

#print axioms q1_l1_1
#print axioms q1_l1_1_uniform
#print axioms q1_l18_recursion
#print axioms q1_l18_horizon
#print axioms q1_l18_fidelity
#print axioms q1_l18_k0
#print axioms q1_l18_fidelity_at_times
#print axioms q1_l18_at_times_satisfiable
#print axioms q1_l12_ledger
#print axioms q1_l12_step1
#print axioms q1_l11_ledger
#print axioms q1_l18_rank_exists
#print axioms q1_l1_1_satisfiable
#print axioms q1_l18_satisfiable
#print axioms summable_tsum_le_of_halving
#print axioms Q1.BR_pos
#print axioms Q1.AR_pos
#print axioms Q1.NR_pos
#print axioms Q1.DR_pos
#print axioms Q1.JR_pos
#print axioms Q1.tR_pos
#print axioms Q1.SR_pos
#print axioms Q1.KR_pos
#print axioms Q1.qR_nonneg
#print axioms Q1.qR_pos
#print axioms Q1.eR0Q_pos
#print axioms Q1.eRcut_pos
#print axioms Q1.eR0Q_cast
#print axioms Q1.eRcut_le_eR0
#print axioms Q1.rate_le_qR
#print axioms Q1.sqrt_pow_two_pow_le
#print axioms Q1.radius_factor_le
#print axioms Q1.tR_cast
#print axioms Q1.BR_pow_le
#print axioms Q1.tR_halving
#print axioms Q1.tR_summable_tsum_le

/-! The cutoff of Lemma 12.2 is a computable rational function: B_R = 5, d' = 2 gives
j_* = 4 and S̄ = 537225/64; the witness instance has a positive cutoff. -/
#eval (Q1.jStar 3 5 2, Q1.SR 3 5 2)
#eval decide (0 < Q1.eRcut 1 1 1 1 0 0 1 1 1 1)

end Flagship1D
