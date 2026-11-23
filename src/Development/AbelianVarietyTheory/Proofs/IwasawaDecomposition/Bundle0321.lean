module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Mathlib
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0323
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0036
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharConjSelfDualFiniteIdelicIffLocal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0312
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0313
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyDeterminant
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.ResidueLocPlace

theorem norm_le_one_of_finite {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
    [Module.Finite ℤ_[p] O] (f : O →+* Qbar p)
    (hf : ∀ z : ℤ_[p], f (algebraMap ℤ_[p] O z) = algebraMap ℚ_[p] (Qbar p) (z : ℚ_[p])) (y : O) :
    ‖f y‖ ≤ 1 := by
  have hy : IsIntegral ℤ_[p] y := Algebra.IsIntegral.isIntegral y
  let v := NormedField.valuation (K := Qbar p)
  have hmem : ∀ z : ℤ_[p], ((algebraMap ℚ_[p] (Qbar p)).comp PadicInt.Coe.ringHom) z ∈ v.integer := by
    intro z
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
    have : ‖algebraMap ℚ_[p] (Qbar p) (z : ℚ_[p])‖ ≤ 1 := by
      rw [PadicAlgCl.norm_extends p]; exact PadicInt.norm_le_one z
    exact_mod_cast this
  let φ : ℤ_[p] →+* v.integer := ((algebraMap ℚ_[p] (Qbar p)).comp PadicInt.Coe.ringHom).codRestrict v.integer hmem
  have hI : IsIntegral v.integer (f y) := by
    refine IsIntegral.map_of_comp_eq φ f ?_ hy
    ext z
    simp only [RingHom.comp_apply, hf]
    rfl
  have h := (Valuation.integer.integers v).mem_of_integral hI
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_lt_one_of_mem_maximalIdeal {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[p] O]
    [Module.Finite ℤ_[p] O] (f : O →+* Qbar p)
    (hf : ∀ z : ℤ_[p], f (algebraMap ℤ_[p] O z) = algebraMap ℚ_[p] (Qbar p) (z : ℚ_[p])) {y : O}
    (hy : y ∈ IsLocalRing.maximalIdeal O) : ‖f y‖ < 1 := by
  have hle : ∀ z : O, ‖f z‖ ≤ 1 := norm_le_one_of_finite f hf
  have hfp : ‖f (p : O)‖ = (p : ℝ)⁻¹ := by
    have h1 := hf (p : ℤ_[p])
    rw [map_natCast] at h1
    rw [h1, PadicAlgCl.norm_extends p]
    simp [Padic.norm_p]
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have hp0 : (p : O) ≠ 0 := by
    intro h; rw [h, map_zero, norm_zero] at hfp
    have : (0 : ℝ) < (p : ℝ)⁻¹ := by
      have := (Fact.out : p.Prime).pos; positivity
    linarith
  have hpu : ¬ IsUnit (p : O) := by
    rintro ⟨u, hu⟩
    have h2 : f (u : O) * f ((u⁻¹ : Oˣ) : O) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have h3 := congrArg norm h2
    rw [norm_mul, norm_one, hu, hfp] at h3
    have h4 := hle ((u⁻¹ : Oˣ) : O)
    have h5 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h4 h5]
  by_cases hy0 : y = 0
  · rw [hy0, map_zero, norm_zero]; exact zero_lt_one
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨e, u, hpe⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hπ
  obtain ⟨k, w, hyk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hπ
  have he : e ≠ 0 := by
    rintro rfl; apply hpu; rw [hpe, pow_zero, mul_one]; exact u.isUnit
  have hk : k ≠ 0 := by
    rintro rfl
    rw [hyk, pow_zero, mul_one] at hy
    exact (IsLocalRing.mem_maximalIdeal _).1 hy w.isUnit
  have hu1 : ‖f (u : O)‖ = 1 := by
    have h2 : f (u : O) * f ((u⁻¹ : Oˣ) : O) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have h3 := congrArg norm h2
    rw [norm_mul, norm_one] at h3
    have h4 := hle ((u⁻¹ : Oˣ) : O)
    have h6 := hle (u : O)
    have h5 : 0 ≤ ‖f (u : O)‖ := norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h4 h5]
  have key : y ^ e * (u : O) ^ k = (p : O) ^ k * (w : O) ^ e := by
    rw [hpe, hyk]; ring
  have hn := congrArg (fun z => ‖f z‖) key
  simp only [map_mul, map_pow, norm_mul, norm_pow, hu1, one_pow, mul_one, hfp] at hn
  have hw := hle (w : O)
  have hA : ‖f y‖ ^ e ≤ ((p : ℝ)⁻¹) ^ k := by
    rw [hn]
    calc ((p : ℝ)⁻¹) ^ k * ‖f (w : O)‖ ^ e ≤ ((p : ℝ)⁻¹) ^ k * 1 := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) hw
      _ = _ := mul_one _
  have hB : ((p : ℝ)⁻¹) ^ k < 1 := pow_lt_one₀ (by positivity) hp1 hk
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) he).1 (lt_of_le_of_lt hA hB)

end GlobalTheory.ResidueLocPlace

namespace GlobalTheory.ResidueLocPlace

theorem exists_residue_lift {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (hp : p.Prime)
    (hq : q.Prime) (ι : Qbar p ≃+* ℂ) (B : ValuationSubring ℂ) (hB : ∀ z, z ∈ B ↔ ‖ι.symm z‖ ≤ 1)
    (κB : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar p)
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[q] O]
    [Module.Finite ℤ_[q] O] (iq : FractionRing O →+* Qbar q)
    (iq_alg : ∀ z : ℤ_[q], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[q] O z)) =
      algebraMap ℚ_[q] (Qbar q) (z : ℚ_[q])) :
    ∃ κ : IsLocalRing.ResidueField O →+* Formalism.CyclotomicNorms.Fbar q, ∀ y : O,
      ∃ hy : (((qCast h ι).toRingHom.comp iq).comp (algebraMap O (FractionRing O))) y ∈ B,
        fbCast h hp hq (κB (IsLocalRing.residue B ⟨_, hy⟩)) = κ (IsLocalRing.residue O y) := by
  subst h
  let f : O →+* Qbar p := iq.comp (algebraMap O (FractionRing O))
  have hf : ∀ z : ℤ_[p], f (algebraMap ℤ_[p] O z) = algebraMap ℚ_[p] (Qbar p) (z : ℚ_[p]) := iq_alg
  have hmem : ∀ y, ι (f y) ∈ B := fun y =>
    (hB _).2 (by rw [RingEquiv.symm_apply_apply]; exact norm_le_one_of_finite f hf y)
  let g : O →+* B := (ι.toRingHom.comp f).codRestrict B.toSubring hmem
  let F : O →+* Formalism.CyclotomicNorms.Fbar p := κB.toRingHom.comp ((IsLocalRing.residue B).comp g)
  have hF : ∀ a ∈ IsLocalRing.maximalIdeal O, F a = 0 := by
    intro a ha
    have hlt := norm_lt_one_of_mem_maximalIdeal f hf ha
    have hg : g a ∈ IsLocalRing.maximalIdeal B := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      rintro ⟨u, hu⟩
      have h1 : ((u : B) : ℂ) * (((u⁻¹ : Bˣ) : B) : ℂ) = 1 := by
        rw [← Subring.coe_mul, Units.mul_inv]; rfl
      rw [hu] at h1
      have h2 : ι (f a) = ((g a : B) : ℂ) := rfl
      rw [← h2] at h1
      have h3 := congrArg (fun z => ‖ι.symm z‖) h1
      simp only [map_mul, RingEquiv.symm_apply_apply, norm_mul, map_one, norm_one] at h3
      have h4 : ‖ι.symm (((u⁻¹ : Bˣ) : B) : ℂ)‖ ≤ 1 := (hB _).1 (((u⁻¹ : Bˣ) : B)).2
      have h5 : 0 ≤ ‖f a‖ := norm_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left h4 h5]
    show κB (IsLocalRing.residue B (g a)) = 0
    rw [(IsLocalRing.residue_eq_zero_iff _).2 hg, map_zero]
  exact ⟨Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) F hF, fun y => ⟨hmem y, rfl⟩⟩

end GlobalTheory.ResidueLocPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyPolarized
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.SphNonSplit

theorem not_split_of_overPl (D : D7) {w w' : PlE D.host} {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))}
    (hw : NG.OverPl w v) (hw' : NG.OverPl w' v) (hs : ¬ IsSplitPl D.host w) : ¬ IsSplitPl D.host w' := by
  intro hs'
  have hu : HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w =
      HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w' :=
    HeightOneSpectrum.ext (hw.trans hw'.symm)
  have hr : Module.finrank (maximalRealSubfield D.host.E) D.host.E = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj D.host.E) hr
      (IsCMField.complexConj_ne_one D.host.E) w' w).1 hu with h | h
  · exact hs (h ▸ hs')
  · have hc : (IsCMField.complexConj D.host.E).toRingEquiv = D.host.conj.toRingEquiv := by
      refine RingEquiv.ext fun x => ?_
      apply D.host.φ₀.injective
      show D.host.φ₀ (IsCMField.complexConj D.host.E x) = D.host.φ₀ (D.host.conj x)
      rw [IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
    rw [hc] at h
    exact hs (GlobalTheory.ConjugatePlaceSplitting.isSplitPl_of_isConjPl hs' ((GlobalTheory.Mem.Chr.conjPl_main.2.1 _ _ w' w).2 h))

theorem split_of_over_g (D : D7) (k : Fin 2) {w : PlE D.host} (hw : w ∈ placesOver D.host.E (D.host.g k)) :
    IsSplitPl D.host w := by
  obtain ⟨u, h | h⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
  · rw [h]; exact GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k u
  · exact GlobalTheory.ConjugatePlaceSplitting.isSplitPl_of_isConjPl (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k u) h

theorem not_mem_bad (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C)
    (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v)
    (w0 : D.what₂.places.Pl) (j : Fin D.R.m) (w : PlE D.host) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))
    (hw : NG.OverPl w v) (hs : ¬ IsSplitPl D.host w) :
    v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw w0) j) := by
  have hg : v ∉ gPl D := by
    rintro ⟨w', hw', k, hk⟩
    exact not_split_of_overPl D hw hw' hs (split_of_over_g D k hk)
  rintro (h | h)
  · exact hg h
  · rw [qPl_tup] at h
    obtain ⟨-, w', hw', hr⟩ := h
    apply not_split_of_overPl D hw hw' hs
    rw [tp.xi_tw] at hr
    by_contra hns
    apply hr
    have hpsi : (tp.psi w0).UnrAt w' := by
      obtain ⟨Q, hQ⟩ := tp.psi_gen w0
      exact (hQ.ram w').2 fun hq => hns (hQ.split w' hq)
    by_cases hl : D.what₂.places.resChar w0 = D.host.pde
    · have hd : cf.del'.UnrAt w' := cf.isDel'.unr w' fun hp => hns (hsp w' (Or.inr hp))
      intro x hx
      simp only [Host.CharFrame.delAt, hl, ↓reduceIte]
      change cf.del'.loc w' x * (tp.psi w0).loc w' x = 1
      rw [hd x hx, hpsi x hx, one_mul]
    · have hd : cf.del.UnrAt w' := cf.isDel.unr w' fun hp => hns (hsp w' (Or.inl hp))
      intro x hx
      simp only [Host.CharFrame.delAt, hl, ↓reduceIte]
      change cf.del.loc w' x * (tp.psi w0).loc w' x = 1
      rw [hd x hx, hpsi x hx, one_mul]

end GlobalTheory.SphNonSplit

namespace GlobalTheory.SphNonSplit

end GlobalTheory.SphNonSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyResidualImage
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.ChiOneRead

theorem localIdele_eq {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (u : (P.adicCompletion E)ˣ) :
    Neutral.B1.localIdele E P u = Units.map (Formalism.L2.NC.locM P) u := by
  classical
  apply Units.ext
  rfl

theorem sqrt_zpow (q : ℕ) (r : ℕ) (t nV : ℕ) (h : nV = r + t) :
    ((Real.sqrt q : ℝ) : ℂ) ^ (-(r : ℤ)) = ((q : ℕ) : ℂ) ^ (((((t : ℝ) - 1) / 2 + (1 - (nV : ℝ)) / 2) : ℝ) : ℂ) := by
  subst h
  have e : (((t : ℝ) - 1) / 2 + (1 - ((r + t : ℕ) : ℝ)) / 2) = -(r : ℝ) / 2 := by push_cast; ring
  rw [e]
  rw [show ((q : ℕ) : ℂ) = ((q : ℝ) : ℂ) by norm_cast, ← Complex.ofReal_cpow (Nat.cast_nonneg _),
    ← Complex.ofReal_zpow]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  push_cast; ring

end GlobalTheory.ChiOneRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharConjSelfDualFiniteIdelicIffLocalStatement
section
open Formalism.BasicNotions Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_conjSelfDual_finite_idelic_iff_local : ∀ {R : Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E), haveI := host_isCMField H; (∀ u : (Af H.E)ˣ, χ.1 (finId H.E (Units.map (conjFin (IsCMField.complexConj H.E).toRingEquiv).toMonoidHom u)⁻¹) = χ.1 (finId H.E u)) ↔ ∀ w w', IsConjPl H w w' → ∀ k : H.Eˣ, χ.locK w' (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.locK w k)⁻¹ := by
  first | exact @GlobalTheory.CuspRep.csdFin_iff | exact GlobalTheory.CuspRep.csdFin_iff | (intros; apply GlobalTheory.CuspRep.csdFin_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharConjSelfDualInfinityInfinitesimalIffFieStatement
section
open Formalism.BasicNotions Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_conjSelfDual_infinity_infinitesimal_iff_field : ∀ {R : Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E), haveI := host_isCMField H; (∀ z, dchi χ (-star z) = dchi χ z) ↔ ∀ k : H.Eˣ, χ.inf (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.inf k)⁻¹ := by
  first | exact @GlobalTheory.CuspRep.csdInf_iff | exact GlobalTheory.CuspRep.csdInf_iff | (intros; apply GlobalTheory.CuspRep.csdInf_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeMultiplicityEqFinrankJointEigenspace
section
noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX
  NumberField IsDedekindDomain Polynomial Module Module.End

section Gen
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

theorem heckeEig_mem_iff_gens (N : NData R H what₂) (i : N.Loc) (x : N.X i)
    (y : TensorProduct (N.O i) (FractionRing (N.O i)) (N.Mt i)) :
    y ∈ heckeEig (N.T i) (N.act i) x ↔ ∀ v k, SplitOut N i v → 1 ≤ k → k ≤ R.nV →
      ((N.act i (N.hT i v k)).baseChange (FractionRing (N.O i))) y =
        algebraMap (N.O i) (FractionRing (N.O i)) ((N.hT i v k : N.X i → N.O i) x) • y := by
  constructor
  · intro hy v k _ _ _
    exact mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hy (N.hT i v k))
  · intro hy
    refine (Submodule.mem_iInf _).2 fun f => mem_eigenspace_iff.2 ?_
    obtain ⟨f, hf⟩ := f
    have hf' := hf
    rw [← N.T_gen i] at hf'
    suffices key : ∀ g (hg' : g ∈ Algebra.adjoin (N.O i) {g : N.X i → N.O i | ∃ v k, IsSplitPl H v ∧
        v ∉ placesOver H.E (N.l i) ∧ v ∉ N.S i ∧ v ∉ N.Q i ∧ 1 ≤ k ∧ k ≤ R.nV ∧
        g = (N.hT i v k : N.X i → N.O i)}), ∀ hg : g ∈ N.T i,
        ((N.act i ⟨g, hg⟩).baseChange (FractionRing (N.O i))) y =
          algebraMap (N.O i) (FractionRing (N.O i)) (g x) • y from key f hf' hf
    intro g hg'
    induction hg' using Algebra.adjoin_induction with
    | mem g hg0 =>
      intro hg
      obtain ⟨v, k, h1, h2, h3, h4, h5, h6, rfl⟩ := hg0
      exact hy v k ⟨h1, h2, h3, h4⟩ h5 h6
    | algebraMap r =>
      intro hg
      have e : (⟨algebraMap (N.O i) (N.X i → N.O i) r, hg⟩ : N.T i) =
          algebraMap (N.O i) (N.T i) r := rfl
      rw [e, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.baseChange_smul,
        LinearMap.baseChange_one]
      simp [algebraMap_smul]
    | add g g' hg1 hg2 ih1 ih2 =>
      intro hg
      have m1 : g ∈ N.T i := N.T_gen i ▸ hg1
      have m2 : g' ∈ N.T i := N.T_gen i ▸ hg2
      have e : (⟨g + g', hg⟩ : N.T i) = ⟨g, m1⟩ + ⟨g', m2⟩ := rfl
      rw [e, map_add (f := _), LinearMap.baseChange_add, LinearMap.add_apply, ih1 m1, ih2 m2, Pi.add_apply, map_add (f := _),
        add_smul]
    | mul g g' hg1 hg2 ih1 ih2 =>
      intro hg
      have m1 : g ∈ N.T i := N.T_gen i ▸ hg1
      have m2 : g' ∈ N.T i := N.T_gen i ▸ hg2
      have e : (⟨g * g', hg⟩ : N.T i) = ⟨g, m1⟩ * ⟨g', m2⟩ := rfl
      rw [e, map_mul, LinearMap.baseChange_mul, Module.End.mul_apply, ih2 m2, LinearMap.map_smul, ih1 m1,
        smul_smul, Pi.mul_apply, map_mul, mul_comm]

end Gen

section Spec
variable {D : D7} {Pl : PlSide D} {M : MtFam D} {C : NChoice D} {big : D.what₂.places.Pl → Finset ℂ}
  {X : LocNd (lay0 D)} {T : LocTw X}

theorem genAt_iff_splitOut (Sp : NdSpec Pl M C big X T) {j : ℕ} {w : D.what₂.places.Pl} {i : X.nd.Loc}
    (h : i ∈ X.nd.locs j w) (v : PlE D.host) (k : ℕ) :
    (SplitOut X.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV) ↔ GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k := by
  obtain ⟨-, h2⟩ := (X.nd.locs_mem j w i).1 h
  have hl : X.nd.l i = D.what₂.places.resChar w := by rw [← X.nd.w_l i, h2]
  have hS : v ∈ X.nd.S i ↔ v ∈ placesS D (D.what₂.places.resChar w) := by
    rw [X.nd.S_def, hl]; rfl
  unfold SplitOut GenAt
  rw [hS, ← Sp.Q_eq j w i h, hl]
  tauto

theorem mult_eq_finrank_jointEig (D : D7) (Pl : PlSide D) (M : MtFam D) (C : NChoice D)
    (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec Pl M C big X T) (j : ℕ)
    (w : D.what₂.places.Pl) (i : X.nd.Loc) (h : i ∈ X.nd.locs j w) (x : X.nd.X i) :
    X.nd.mult i x = Module.finrank (FractionRing (Sp.B.Oc j w)) ↥(⨅ (v : PlE D.host) (k : ℕ)
      (_ : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k),
      Module.End.eigenspace (Sp.B.hK j w v k) (algebraMap (Sp.B.Oc j w) (FractionRing (Sp.B.Oc j w))
        (Sp.phO j w i h ((X.nd.hT i v k : X.nd.X i → X.nd.O i) x)))) := by
  set Fam := (⨅ (v : PlE D.host) (k : ℕ) (_ : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k),
      Module.End.eigenspace (Sp.B.hK j w v k) (algebraMap (Sp.B.Oc j w) (FractionRing (Sp.B.Oc j w))
        (Sp.phO j w i h ((X.nd.hT i v k : X.nd.X i → X.nd.O i) x)))) with hFam_def
  have hFam : ∀ e, e ∈ Fam ↔ ∀ v k, GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k →
      Sp.B.hK j w v k e = algebraMap (Sp.B.Oc j w) (FractionRing (Sp.B.Oc j w))
        (Sp.phO j w i h ((X.nd.hT i v k : X.nd.X i → X.nd.O i) x)) • e := by
    intro e
    simp only [Fam, Submodule.mem_iInf, mem_eigenspace_iff]
  have hval : ∀ v k (hvk : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k),
      algebraMap (Sp.B.Oc j w) (FractionRing (Sp.B.Oc j w))
        (Sp.phO j w i h ((X.nd.hT i v k : X.nd.X i → X.nd.O i) x)) =
      NCov.pt (Sp.ptX j w i h x).1 ⟨Sp.B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ := by
    intro v k hvk
    simp only [NCov.pt]
    rw [Sp.ptX_hT j w i h x v k hvk]
  have hE : ∀ e, e ∈ Fam ↔ e ∈ NCov.E (Formalism.L2.heckeAlg Sp.B j w) (Sp.ptX j w i h x).1 := by
    intro e
    rw [hFam, NCov.mem_E_iff]
    constructor
    · rintro hy _ ⟨v, k, hvk, rfl⟩
      rw [← hval v k hvk]
      exact hy v k hvk
    · intro hy v k hvk
      rw [hval v k hvk]
      exact hy _ ⟨v, k, hvk, rfl⟩
  have hpsi : ∀ y, y ∈ heckeEig (X.nd.T i) (X.nd.act i) x ↔ Sp.Psi j w i h y ∈ Fam := by
    intro y
    rw [heckeEig_mem_iff_gens, hFam]
    constructor
    · intro hy v k hvk
      obtain ⟨hso, hk1, hk2⟩ := (genAt_iff_splitOut Sp h v k).2 hvk
      have e := congrArg (Sp.Psi j w i h) (hy v k hso hk1 hk2)
      rw [Sp.act_hK j w i h v k hvk, LinearMap.map_smulₛₗ] at e
      rw [e]
      congr 1
      exact Sp.phK_alg j w i h _
    · intro hy v k hso hk1 hk2
      have hvk := (genAt_iff_splitOut Sp h v k).1 ⟨hso, hk1, hk2⟩
      apply Sp.Psi_inj j w i h
      rw [Sp.act_hK j w i h v k hvk, LinearMap.map_smulₛₗ, hy v k hvk]
      congr 1
      exact (Sp.phK_alg j w i h _).symm
  let f : ↥(heckeEig (X.nd.T i) (X.nd.act i) x) →ₛₗ[(Sp.phK j w i h).toRingHom] Sp.B.V j w :=
    (Sp.Psi j w i h).comp (heckeEig (X.nd.T i) (X.nd.act i) x).subtype
  change Module.finrank _ ↥(heckeEig (X.nd.T i) (X.nd.act i) x) = _
  refine finrank_eq_of_semilinear (Sp.phK j w i h) f Fam ?_ ?_
  · intro a b hab
    exact Subtype.ext (Sp.Psi_inj j w i h hab)
  · intro e
    constructor
    · intro he
      have hp : e ∈ NCov.part (Formalism.L2.heckeAlg Sp.B j w) (Sp.mx j w i) := by
        have := NCov.E_le_part (Formalism.L2.heckeAlg Sp.B j w) (Sp.ptX j w i h x).1 ((hE e).1 he)
        rwa [(Sp.ptX j w i h x).2.1] at this
      obtain ⟨z, rfl⟩ := (Sp.Psi_range j w i h e).1 hp
      exact ⟨⟨z, (hpsi z).2 he⟩, rfl⟩
    · rintro ⟨⟨z, hz⟩, rfl⟩
      exact (hpsi z).1 hz

end Spec

end GlobalTheory.HeightCounting
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostPrimesOverLevelPlaceStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.host_primes_over_level_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u v (q : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E)), q.under (𝓞 (I.rec7 l Z).host.F) = ((F u).atT.eV v).1 → q.asIdeal = (F u).atT.Pv v ∨ q.asIdeal = Formalism.HermitianLatticesTheory.conjIdeal (K := (I.rec7 l Z).host.E) ((F u).atT.Pv v) := by
  first | exact @GlobalTheory.Mem.Col2.HAt.primes_over_level_place | exact GlobalTheory.Mem.Col2.HAt.primes_over_level_place | (intros; apply GlobalTheory.Mem.Col2.HAt.primes_over_level_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaWildOfTrivialTameCharactersStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_wild_of_trivial_tame_characters : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ∀ τ ∈ Ine (F := E) A, (∀ d, 0 < d → ∃ y : Ω, y ^ (g ^ d - 1) = ((g : ℕ) : Ω) ∧ A.valuation (τ y / y - 1) < 1) → ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1 := by
  first | exact @GlobalTheory.TameWild.cob_lt_one_of_tame | exact GlobalTheory.TameWild.cob_lt_one_of_tame | (intros; apply GlobalTheory.TameWild.cob_lt_one_of_tame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalCondMoveDecoratedLattice
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.TC.ChTw.Match

variable {B : Base} {X : PreX B.toPre}

def LocalCondMoveDecoratedLattice (u : B.Word) (n : ℕ) (s : GA B n) (h : GLG (E := B.fields.E) (n := n) (SG := (B.primes X).vGs)) : Prop :=
  s ∈ Formalism.L2.Herm.UstdAf B.sp.cm n ∧ Formalism.L2.Herm.Carries s (stdLat B.fields.E n) (stdLat B.fields.E n) ∧
  (∀ (P : (B.primes X).vT u) (r j : Fin n), r.1 + 1 = n →
    HasRes P.1 (adAt B.host.F P.1 ((s⁻¹ : GA B n).1 r j)) (if j = r then 1 else 0)) ∧
  ∀ (w : (B.primes X).vGs) (r j : Fin n), HasRes w.1 (adAt B.host.F w.1 ((s⁻¹ : GA B n).1 r j)) ((h w).1 r j)

def LocCQ (Q : Finset (HeightOneSpectrum (𝓞 B.fields.E))) (n : ℕ) (s : GA B n) (θ : GLQ B.fields.E n Q) : Prop :=
  ∀ (P : Q) (r j : Fin n), adAt B.host.F P.1 ((s : Matrix (Fin n) (Fin n) _) r j) =
    algebraMap B.host.E _ ((((θ P)⁻¹ : ↥(GLint B.fields.E n P.1)).1) (Pi.single j 1) r)

end GlobalTheory.Mem.Col2.TC.ChTw.Match
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownLevelFunctionalEqStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.move_down_level_functional_eq : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → ∀ (γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)), (γ.1 : GL (Fin (B.R.N i)) B.fields.E) = (I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) → ∀ (x : ↥(LdG (I.rec7 l Z) i hi (latCrd (I.rec7 l Z) i hi (I.latAt u a i ((I.fm l u a).dn i v c.1 g))))) (hx : γ.1.1 *ᵥ x.1 ∈ LkG (I.rec7 l Z) i hi (PvG (I.resT l u a) v) (latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))), (I.fm l u a).fv i v _ (L.pr v _ x) = g (L.prk v c.1 ⟨_, hx⟩) := by
  set_option maxHeartbeats 8000000 in
    exact @GlobalTheory.Mem.Col2.TC.dn_level_functional
end

