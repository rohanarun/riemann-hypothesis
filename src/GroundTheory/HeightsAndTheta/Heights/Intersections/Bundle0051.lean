module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0050
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0037
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocResidueDeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem SemilocResidueDeg.proof (hDim : SemilocResidueFibreDim.Statement) (hAdj : SemilocResidueAdjoin.Statement) :
    SemilocResidueDeg.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hZ hs hsP hW W' hW' _ G' J' hJ
  have hrel : ∀ k', ∃ i, (X ⟨k', i⟩ : MRing ι') ∉ W' := hW'.1.2.2
  choose i' hi' using hrel
  have hfib : IsProjVarF (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G') 0 := hDim K ι K' ι' κ v P' n s α W hv hP' hZ hs hsP hW W' hW' G'
  have hz : ∀ k : FibreBlock κ, G'.x' ⟨k.1, i' k.1⟩ ≠ 0 := by
    intro k h0
    apply hi' k.1
    rw [← G'.genericFibre_ker_target, RingHom.mem_ker, aeval_X]
    exact h0
  have hj : IsChart (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G') (fun k => i' k.1) := by
    intro k hk
    apply hz k
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X] at hk
    exact hk
  refine ⟨_, hAdj K ι K' ι' κ v P' n s α W hv hP' hZ hs hsP hW W' hW' G' i' hi', ?_⟩
  rw [hJ.1 _ Fin.elim0 _ hfib hj]
  exact congrArg _ (ChartRankAdjoin.proof (FibreBlock κ) (fibreIdx ι' κ) G'.Φ G'.Φ' (fun q => G'.x' ⟨q.1.1, q.2⟩)
    (fun k => i' k.1) hz hfib.1.2.1).symm

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocResidueFibreDim
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 PointVertical

theorem SemilocResidueFibreDim.proof (hFD : FibreDivSupp.Statement) (hDim : FibreDimStatement)
    (hAI : FibreDimensionZero.Statement) : SemilocResidueFibreDim.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hZ hs hsP hW W' hW' G'
  classical
  have hsW : s ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  have hsW' : rename v s ∈ W' := by
    have h : s ∈ imageZ v W' := hW'.2.2 ▸ hsW
    exact h
  have hD' : W' ∈ divSupp P' (rename v s) := ((hFD K ι K' ι' κ v P' n s α W hv hP' hZ hs hsP hW W').1 ⟨hW', hsW'⟩).1
  have hsec' : IsSectionOn P' (HermLine.sqMetric (ι := ι') (Function.extend κ α 0)) (rename v s) :=
    ⟨Function.extend κ α 0, fun _ => rfl, isMultiHomog_rename hv hs, hsP⟩
  have hsec : IsSectionOn (imageZ v P') (HermLine.sqMetric (ι := ι) α) s := ⟨α, fun _ => rfl, hs, hsP⟩
  have divSuppArith : DivSuppArithStatement := by
    intro K _ ι _ P n A s W hP hs hW
    obtain ⟨hK, ⟨hPp, hPh, -⟩, -, hPdim⟩ := hP
    obtain ⟨a, -, hsa, hsP⟩ := hs
    obtain ⟨hWmin, hWrel⟩ := hW
    have hWp : W.IsPrime := hWmin.1.1
    have hWmh : IsMultiHomogIdeal W := isMultiHomogIdeal_of_mem_minimalPrimes hPh hsa hWmin
    have := hPp
    have h1 := dim_quot_minimal_add_one P W s hsP hWmin
    rw [hPdim] at h1
    have hdim : ringKrullDim (MRing ι ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) :=
      withBot_eq_of_add_one (by rw [h1, show n + 1 + Fintype.card K = n + Fintype.card K + 1 by omega])
    exact ⟨fun hh => ⟨hK, ⟨hWp, hWmh, hWrel⟩, hh, hdim⟩,
      fun hv => ⟨⟨hWp, hWmh, hWrel⟩, charOf_prime hWp hv, hdim⟩⟩
  have hA' := divSuppArith K' ι' P' n _ _ W' hP' hsec' hD'
  have hA := divSuppArith K ι (imageZ v P') n _ _ W hZ hsec hW
  have hdW : ringKrullDim (MRing ι ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    by_cases hh : IsHorizontal W
    · exact (hA.1 hh).2.2.2
    · exact (hA.2 hh).2.2
  by_cases hh' : IsHorizontal W'
  · have hh : IsHorizontal W := by
      unfold IsHorizontal at hh' ⊢
      rw [← hh', ← hW'.2.2]
      ext z
      simp [imageZ, Ideal.mem_comap]
    have hW'a : IsArithVar W' (n + 0) := hA'.1 hh'
    have hWa : IsArithVar (imageZ v W') n := hW'.2.2 ▸ hA.1 hh
    exact hDim K ι K' ι' κ v W' n 0 G' hv hW'a hWa
  · obtain ⟨hW'm, hpr, hdW'⟩ := hA'.2 hh'
    set p := charOf W' with hpdef
    have : Fact p.Prime := ⟨hpr⟩
    have hpW' : ((p : ℕ) : MRing ι') ∈ W' := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.natCast_mem_of_charOf W'
    have hpW : ((p : ℕ) : MRing ι) ∈ W := by
      rw [← hW'.2.2]
      show rename v ((p : ℕ) : MRing ι) ∈ W'
      simpa using hpW'
    have hWm : IsMultiProjPrime W := hW'.2.2 ▸ isMultiProjPrime_imageZ hv hW'm
    have hWp : IsProjVarF (W'.map (red p)) n :=
      ⟨isMultiProjPrime_red p hW'm hpW', by rw [ringKrullDim_red p hpW', hdW']⟩
    have hVi : IsProjVarF (imageVar (ZMod p) v (W'.map (red p))) n := by
      rw [imageVar_red p v hpW', hW'.2.2]
      exact ⟨isMultiProjPrime_red p hWm hpW, by rw [ringKrullDim_red p hpW, hdW]⟩
    exact hAI K ι K' ι' κ v p W' n hv hpW' hWp hVi G'

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StSemilocResidueFrac
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

theorem primeSubfield_exists_div {E : Type*} [Field E] (c : (⊥ : Subfield E)) :
    ∃ a b : ℤ, (b : (⊥ : Subfield E)) ≠ 0 ∧ c = a / b := by
  have hc : (c : E) ∈ Subfield.closure (∅ : Set E) := by
    rw [Subfield.closure_empty]
    exact c.2
  obtain ⟨y, hy, z, hz, h⟩ := Subfield.mem_closure_iff.1 hc
  rw [Subring.closure_empty, Subring.mem_bot] at hy hz
  obtain ⟨a, rfl⟩ := hy
  obtain ⟨b, rfl⟩ := hz
  by_cases hb : (b : E) = 0
  · refine ⟨0, 1, by simp, Subtype.ext ?_⟩
    simp [← h, hb]
  · refine ⟨a, b, fun h0 => hb ?_, Subtype.ext ?_⟩
    · simpa using congrArg Subtype.val h0
    · simp [← h]

def SemilocResidueFrac.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)) (hv : IsBlockMap κ v) (hP' : IsArithVar P' (n + 1)),
    IsArithVar (imageZ v P') (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    ∀ (W' : Ideal (MRing ι')) (hW' : W' ∈ fibreOver v P' W) [IsLocalRing (locRing P' W')]
      (G' : GenFibre v W') (i' : ∀ k', ι' k'), (∀ k', (X ⟨k', i' k'⟩ : MRing ι') ∉ W') →
    ∀ (F : Type) [Field F] [Algebra F G'.Φ'], (∀ c : F, ∃ a b : ℤ, (b : F) ≠ 0 ∧ c = a / b) →
    haveI := hP'.2.1.1
    letI := (locToSemiloc hv P' W).toAlgebra
    Module.length (locRing (imageZ v P') W)
        (semiLocRing P' (fibreOver v P' W) ⧸ semiMaxIdeal P' (fibreOver v P' W) W' hW') =
      (IntermediateField.relfinrank
        (IntermediateField.adjoin F
          (Set.range ((fun q : Σ k', ι' k' => G'.x' q / G'.x' ⟨q.1, i' q.1⟩) ∘ v)))
        (IntermediateField.adjoin F (Set.range fun q : Σ k', ι' k' => G'.x' q / G'.x' ⟨q.1, i' q.1⟩)) : ℕ∞)

end GroundTheory.Heights₂.Heights.Inter
end
end

