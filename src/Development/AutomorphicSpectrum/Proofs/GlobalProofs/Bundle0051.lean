module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1189
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1470
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0024
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0028
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0030
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0022
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0025
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIrreducibleOfJhMultEqOne
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0043
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsDistinctCuspidalPairEmbedding
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIrreducibleOfClsGLEqSingle
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0389
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0030

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RationalUnipotentLeParabolic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin

open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev

theorem ratPts_unip_le_leftSub : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ S T : Finset (Fin m), S ⊆ T →
      GQ V ⊓ unip D.sp.cm.sig V.gram X T ≤ leftSub V X Y S := by
  intro D V m X Y hW S T hST
  have hCM := Formalism.MainNotions.UnusedSlot34.isCMExt_D D
  have hH := Orb.isHermND_gram V
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS
    intro g hg
    rw [Subgroup.mem_inf] at hg
    unfold leftSub
    apply Subgroup.mem_sup_right
    refine Subgroup.mem_inf.2 ⟨hg.1, ?_⟩
    simp [GlobalTheory.StdPar.levi]
  · have hkS : S.max' hS ∈ S := S.max'_mem hS
    have hle : ∀ j ∈ S, j ≤ S.max' hS := fun j hj => S.le_max' j hj
    have hs : ((S.max' hS : Fin m) : ℕ) + 1 ≤ m := (S.max' hS).isLt
    have hiff : ∀ i : Fin m, (i : ℕ) < (S.max' hS : ℕ) + 1 ↔ ∃ j ∈ S, i ≤ j := by
      intro i
      constructor
      · intro hi
        exact ⟨S.max' hS, hkS, Fin.le_iff_val_le_val.2 (Nat.lt_succ_iff.1 hi)⟩
      · rintro ⟨j, hj, hij⟩
        have h1 := Fin.le_iff_val_le_val.1 hij
        have h2 := Fin.le_iff_val_le_val.1 (hle j hj)
        omega
    obtain ⟨hU, hL, -⟩ := GlobalTheory.TieStd.stdPar_eq_flag _ _ D.sp.cm.sig hCM _ V.gram hH m X Y hW S (((S.max' hS : Fin m) : ℕ) + 1) hs hiff
      (fun i => ({x ∈ S | x < Fin.castLE hs i} : Finset (Fin m)).card) (fun _ => rfl)
    have hpar := GlobalTheory.ConstTrans.unip_le_parFlag _ _ D.sp.cm.sig hCM _ V.gram hH m X Y hW T S (S.max' hS) hST hkS hle
    have hxx : Formalism.UG.cT (↑D.sp.cm.sig) (X.submatrix id (Fin.castLE hs)) * V.gram * X.submatrix id (Fin.castLE hs) = 0 := by
      ext i j
      have := congrFun (congrFun hW.xx (Fin.castLE hs i)) (Fin.castLE hs j)
      simpa [Formalism.UG.cT, Matrix.mul_apply] using this
    have hyy : Formalism.UG.cT (↑D.sp.cm.sig) (Y.submatrix id (Fin.castLE hs)) * V.gram * Y.submatrix id (Fin.castLE hs) = 0 := by
      ext i j
      have := congrFun (congrFun hW.yy (Fin.castLE hs i)) (Fin.castLE hs j)
      simpa [Formalism.UG.cT, Matrix.mul_apply] using this
    have hxy : Formalism.UG.cT (↑D.sp.cm.sig) (X.submatrix id (Fin.castLE hs)) * V.gram * Y.submatrix id (Fin.castLE hs) = 1 := by
      ext i j
      have := congrFun (congrFun hW.xy (Fin.castLE hs i)) (Fin.castLE hs j)
      simpa [Formalism.UG.cT, Matrix.mul_apply, Matrix.one_apply, Fin.ext_iff] using this
    obtain ⟨hdec, -⟩ := GlobalTheory.LeviFlag.levi_decomposition _ _ D.sp.cm.sig hCM _ V.gram hH _
      (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs))
      (fun i => ({x ∈ S | x < Fin.castLE hs i} : Finset (Fin m)).card) hxx hyy hxy
    intro g hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hgQ, hgT⟩ := hg
    have hp := hpar hgT
    obtain ⟨u, hu, l, hl, rfl, hrat⟩ := hdec g hp
    unfold leftSub
    rw [hU, hL]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hrat hgQ, hl⟩))

end GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SelfDualTransport
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth

section Gen
open NumberField IsDedekindDomain MeasureTheory
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix GroundTheory.Heights₂.Theta
open scoped TensorProduct ENNReal Matrix NumberField.AdeleRing

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_test : ∃ f ∈ schwartzBruhatPi (K := F) (ι := ι), HasCompactSupport f ∧ f 0 ≠ 0 := GlobalTheory.T.exists_schwartzBruhat_compact_support_nonzero F ι

theorem selfDual_eq (G : Matrix ι ι F) (hs : G.IsSymm) (hG : G.det ≠ 0) (ν : Measure (ι → 𝔸[F]))
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.SelfDual ν (chiG G)) : ν = adeleMeasurePi F := by
  obtain ⟨f0, hf0, hcs, h0⟩ := exists_test (F := F) (ι := ι)
  have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
  have hNM : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hu
  have hMN : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hu
  set Gm := G.map (algebraMap F 𝔸[F]) with hGm
  have hH := h.1
  have e : ν = Measure.addHaarScalarFactor ν (adeleMeasurePi F) • adeleMeasurePi F :=
    Measure.isAddLeftInvariant_eq_smul ν (adeleMeasurePi F)
  set c : NNReal := Measure.addHaarScalarFactor ν (adeleMeasurePi F) with hcdef

  have hT0 : ∀ (g : (ι → 𝔸[F]) → ℂ) y, ∫ x, g x * chiG G x y ∂(adeleMeasurePi F) = adelicFourierPi F g (Gm *ᵥ y) := fun g y => rfl
  have hT : ∀ (g : (ι → 𝔸[F]) → ℂ) y, ∫ x, g x * chiG G x y ∂ν = (c : ℂ) * adelicFourierPi F g (Gm *ᵥ y) := by
    intro g y
    rw [e, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, hT0]
  set g1 : (ι → 𝔸[F]) → ℂ := fun y => adelicFourierPi F f0 (Gm *ᵥ y) with hg1
  have hg1m : g1 ∈ schwartzBruhatPi (K := F) (ι := ι) :=
    comp_mulVec_mem_schwartzBruhatPi G G⁻¹ hNM hMN (adelicFourierPi_mem_schwartzBruhatPi hf0)
  have hI : Integrable (fun y => ∫ x, f0 x * chiG G x y ∂ν) ν := by
    simp only [hT]
    rw [e]
    exact ((integrable_of_mem_schwartzBruhatPi hg1m).const_mul (c : ℂ)).smul_measure_nnreal
  have h2 := h.2 f0 (continuous_of_mem_schwartzBruhatPi hf0) hcs hI 0
  simp only [hT] at h2
  have h3 : adelicFourierPi F (fun x => (c : ℂ) * adelicFourierPi F f0 (Gm *ᵥ x)) (Gm *ᵥ 0) =
      (c : ℂ) * adelicFourierPi F g1 (Gm *ᵥ 0) :=
    congrFun (adelicFourierPi_smul (c : ℂ) g1) _
  have h4 : adelicFourierPi F g1 (Gm *ᵥ 0) = f0 0 := by
    rw [Matrix.mulVec_zero, hg1, adelicFourierPi_comp_mulVec G G⁻¹ hNM hMN, Matrix.mulVec_zero,
      adelicFourierPi_adelicFourierPi hf0]
    simp
  rw [h3, h4, neg_zero, ← mul_assoc] at h2
  have h5 : ((c : ℂ)) * (c : ℂ) = 1 := mul_right_cancel₀ h0 (by rw [h2, one_mul])
  have h6 : c * c = 1 := by exact_mod_cast h5
  have h7 : c = 1 := by
    have : (c : ℝ) * c = 1 := by exact_mod_cast h6
    have h8 : (c : ℝ) = 1 := by nlinarith [c.coe_nonneg]
    exact_mod_cast h8
  rw [e, h7, one_smul]

theorem selfDual_transport {V V' : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup V'] [TopologicalSpace V'] [IsTopologicalAddGroup V']
    [MeasurableSpace V'] [BorelSpace V'] (e : V ≃ₜ V') (he : ∀ x y, e (x + y) = e x + e y)
    (χ : V → V → ℂ) (χ' : V' → V' → ℂ) (hχ : ∀ x y, χ' (e x) (e y) = χ x y) (μ : Measure V)
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.SelfDual μ χ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.SelfDual (μ.map e) χ' := by
  have hμ := h.1
  let a : V ≃+ V' := AddEquiv.mk' e.toEquiv he
  have ha : ∀ x, a x = e x := fun _ => rfl
  refine ⟨a.isAddHaarMeasure_map μ e.continuous e.symm.continuous, fun Φ hc hs hI z => ?_⟩
  have hemb := e.measurableEmbedding
  set Φ0 : V → ℂ := fun x => Φ (e x) with hΦ0
  have hT : ∀ y, ∫ x, Φ x * χ' x (e y) ∂(μ.map e) = ∫ x, Φ0 x * χ x y ∂μ := by
    intro y
    rw [hemb.integral_map]
    simp only [hΦ0, hχ]
  have hI' : Integrable (fun y => ∫ x, Φ0 x * χ x y ∂μ) μ := by
    have h1 := (hemb.integrable_map_iff).1 hI
    exact h1.congr (Filter.Eventually.of_forall fun y => by simp only [Function.comp_apply, hT])
  have h2 := h.2 Φ0 (hc.comp e.continuous) (hs.comp_homeomorph e) hI' (e.symm z)
  rw [hemb.integral_map]
  have h3 : Φ0 (-e.symm z) = Φ (-z) := by
    simp only [hΦ0]
    rw [← ha, map_neg, ha, e.apply_symm_apply]
  rw [← h3, ← h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only []
  rw [hT y, ← hχ y (e.symm z), e.apply_symm_apply]

end Gen

section Link
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix GroundTheory.Heights₂.Theta
open GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.CoordMat
open scoped TensorProduct ENNReal Matrix NumberField.AdeleRing
attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end Link

section Main
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

end Main
end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.TotallyDisjointProductIrreducibleOfPolynomialRin
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.TDZ

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.LocGL.SupportUnique GlobalTheory.SplitRead GlobalTheory.JHMult
open GlobalTheory.CompanionTheory.Hypotheses₂.TD

set_option synthInstance.maxHeartbeats 400000

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem commute_pair (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness)
    (hZ : ZelevinskyPolynomialRing) (g : Fin 2 → IrrGL (k := k)) (h0 : (g 0).IsCusp) (h1 : (g 1).IsCusp)
    (hU : ∀ j : ℤ, |j| ≤ 1 → g 0 ≠ (g 1).nu (j : ℂ)) {n : Type} [Fintype n] [DecidableEq n]
    (f : (Σ i, Fin (g i).1) ≃ n) (f' : (Σ i, Fin (g (Equiv.swap 0 1 i)).1) ≃ n) :
    Nonempty ((multiProd f fun i => (g i).rep).Equiv (multiProd f' fun i => (g (Equiv.swap 0 1 i)).rep)) := by
  let σ : ∀ i, Irr k (g i).1 := fun i => Irr.ofIrrRep (g i).2.rep
  have hc : ∀ i, (g i).IsCusp := fun i => by
    fin_cases i
    · exact h0
    · exact h1
  have i1 : (multiProd f fun i => (σ i).π).IsIrreducible :=
    isIrreducible_multiProd_of_prod₂ (fun i => (g i).1) σ
      (GlobalTheory.CompanionTheory.Hypotheses₂.RankOne.isIrreducible_prod₂_of_polynomialRing hG hBZ hZ k (g 0) (g 1) h0 h1 hU) f
  have g0 : g (Equiv.swap 0 1 0) = g 1 := by simp
  have g1 : g (Equiv.swap 0 1 1) = g 0 := by simp
  have i2 : (multiProd f' fun i => (σ (Equiv.swap 0 1 i)).π).IsIrreducible :=
    isIrreducible_multiProd_of_prod₂ (fun i => (g (Equiv.swap 0 1 i)).1) (fun i => σ (Equiv.swap 0 1 i))
      (GlobalTheory.CompanionTheory.Hypotheses₂.RankOne.isIrreducible_prod₂_of_polynomialRing hG hBZ hZ k _ _ (hc _) (hc _) (by
        rw [g0, g1]
        exact unlinked_symm hU)) f'
  refine GlobalTheory.CompanionTheory.Hypotheses₂.TDSwap.swap_equiv_of_irreducible hG hBZ k n (fun i => (g i).1) σ
    (fun i => ⟨(hc i).1, (hc i).2⟩) ?_ f f' i1 i2
  show IrrGL.of (g 0).rep (g 0).2.rep.smooth (g 0).2.rep.irr ≠ IrrGL.of (g 1).rep (g 1).2.rep.smooth (g 1).2.rep.irr
  rw [IrrGL.of_rep, IrrGL.of_rep]
  have := hU 0 (by simp)
  simpa using this

theorem occurs (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness)
    (hZ : ZelevinskyPolynomialRing) {d : Fin 2 → ℕ}
    (p : ∀ i, Irr k (d i)) {A : Fin 2 → Multiset (IrrGL (k := k))} (hA : ∀ i, HasSupport (p i).π (A i))
    (hAB : ∀ x ∈ A 0, x ∉ A 1) (hU : ∀ x ∈ A 0, ∀ y ∈ A 1, ∀ j : ℤ, |j| ≤ 1 → x ≠ y.nu (j : ℂ))
    (e : (Σ i, Fin (d i)) ≃ Fin (d 0 + d 1)) (Q : Irr k (d 0 + d 1))
    (hQ : IsSubquotient Q.π (multiProd e fun i => (p i).π)) :
    IsSubquotient (piTensor fun i => (p i).π) (GlobalTheory.SmGL.jac e Q.π) := by
  classical
  obtain ⟨s, u, e₃, hc, φ, hφ⟩ := GlobalTheory.CompanionTheory.CuspEmbed.main hBZ hG k _ Q
  have hS₁ : HasSupport Q.π (Finset.univ.val.map u) :=
    ⟨s, u, rfl, Q.irr, fun a => ⟨(hc a).1, (u a).2.rep.irr, (hc a).2⟩, e₃, .of_injective φ hφ⟩
  have hd : ∑ i, d i = d 0 + d 1 := Fin.sum_univ_two d
  have hS₂ : HasSupport Q.π (A 0 + A 1) := by
    obtain ⟨φ'⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ e (stdBlocks d hd) _).1
      (piTensor fun i => (p i).π)
    let ψ := φ'.trans (prodIrrEquiv hd (fun i => (p i).π) (fun i => (p i).smooth) fun i => (p i).irr)
    have h := hasSupport_of_isSubquotient_prodIrr
      (y := fun i => IrrGL.of (p i).π (p i).smooth (p i).irr)
      (fun i => (hA i).of_equiv (IrrGL.equivOf _ _ _)) Q.irr
      (hQ.trans (.of_injective ψ.toIntertwiningMap ψ.toLinearEquiv.injective))
    rwa [Fin.sum_univ_two] at h
  have hm : Finset.univ.val.map u = A 0 + A 1 := hasSupport_unique hG hBZ hS₁ hS₂
  let S : Finset (Fin s) := Finset.univ.filter fun a => u a ∈ A 1
  let σ : ∀ a, Irr k (u a).1 := fun a => Irr.ofIrrRep (u a).2.rep
  have mem : ∀ a, u a ∈ A 0 ∨ u a ∈ A 1 := fun a =>
    Multiset.mem_add.1 (hm ▸ Multiset.mem_map_of_mem u (Finset.mem_univ a))
  have mem1 : ∀ a, a ∈ S → u a ∈ A 1 := fun a ha => (Finset.mem_filter.1 ha).2
  have mem0 : ∀ a, a ∉ S → u a ∈ A 0 := fun a ha =>
    (mem a).resolve_right fun h => ha (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  have mS : S.val.map u = A 1 := by
    have h : S.val.map u = (Finset.univ.val.map u).filter (· ∈ A 1) := by
      rw [Multiset.filter_map]
      rfl
    rw [h, hm, Multiset.filter_add, Multiset.filter_eq_nil.2 (fun x hx => hAB x hx),
      Multiset.filter_eq_self.2 (fun x hx => hx), zero_add]
  have mC : Sᶜ.val.map u = A 0 := by
    have h : Sᶜ.val.map u = (Finset.univ.val.map u).filter (· ∉ A 1) := by
      rw [Multiset.filter_map, Finset.compl_filter]
      rfl
    rw [h, hm, Multiset.filter_add, Multiset.filter_eq_self.2 (fun x hx => hAB x hx),
      Multiset.filter_eq_nil.2 (fun x hx h => h hx), add_zero]
  have deg : ∀ (T : Finset (Fin s)) (C : Multiset (IrrGL (k := k))), T.val.map u = C →
      ∑ a : Fin T.card, (u (T.orderEmbOfFin rfl a)).1 = (C.map Sigma.fst).sum := by
    intro T C h
    rw [← h, ← map_orderEmb T u, Multiset.map_map]
    rfl
  have c₁ : Fintype.card (Σ a : Fin Sᶜ.card, Fin (u (Sᶜ.orderEmbOfFin rfl a)).1) = Fintype.card (Fin (d 0)) := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [deg _ _ mC, (hA 0).sum_fst, Fintype.card_fin]
  have c₂ : Fintype.card (Σ a : Fin S.card, Fin (u (S.orderEmbOfFin rfl a)).1) = Fintype.card (Fin (d 1)) := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [deg _ _ mS, (hA 1).sum_fst, Fintype.card_fin]
  let e₁ := Fintype.equivOfCardEq c₁
  let e₂ := Fintype.equivOfCardEq c₂
  obtain ⟨Φ⟩ := _root_.GlobalTheory.ProdReorder.reorder_split k s (fun a => (u a).1) σ S (d 0) (d 1) e₃ e₁ e₂
    (fun a b ha hb n _ _ f f' => commute_pair hG hBZ hZ (fun i => u (![a, b] i)) (hc a) (hc b)
      (hU _ (mem0 a ha) _ (mem1 b hb)) f f')
  have hsupp : ∀ (T : Finset (Fin s)) (C : Multiset (IrrGL (k := k))), T.val.map u = C → ∀ (n : ℕ)
      (f : (Σ a : Fin T.card, Fin (u (T.orderEmbOfFin rfl a)).1) ≃ Fin n)
      (y : IrrRep (GL (Fin n) k)), IsSubquotient y.ρ (multiProd f fun a => (σ (T.orderEmbOfFin rfl a)).π) →
      HasSupport y.ρ C := by
    intro T C hT n f y hy
    refine ⟨T.card, fun a => u (T.orderEmbOfFin rfl a), ?_, y.irr,
      fun a => ⟨(hc _).1, (u _).2.rep.irr, (hc _).2⟩, f, hy⟩
    rw [map_orderEmb, hT]
  exact occurs_of_prod₂ hG hBZ p hA hAB e Q hQ
    ⟨_, multiProd e₁ fun a => (σ (Sᶜ.orderEmbOfFin rfl a)).π, isSmooth_parInd _ _⟩
    ⟨_, multiProd e₂ fun a => (σ (S.orderEmbOfFin rfl a)).π, isSmooth_parInd _ _⟩
    (hsupp _ _ mC _ e₁) (hsupp _ _ mS _ e₂) (Φ.toIntertwiningMap.comp φ) (Φ.toLinearEquiv.injective.comp hφ)

theorem isIrreducible_prod₂ (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness)
    (hZ : ZelevinskyPolynomialRing) {r t : ℕ} (π₁ : Irr k r) (π₂ : Irr k t)
    {A₀ A₁ : Multiset (IrrGL (k := k))} (H₁ : HasSupport π₁.π A₀) (H₂ : HasSupport π₂.π A₁)
    (hU : ∀ x ∈ A₀, ∀ y ∈ A₁, ∀ j : ℤ, |j| ≤ 1 → x ≠ y.nu (j : ℂ)) :
    (prod₂ π₁.π π₂.π).IsIrreducible := by
  have hAB : ∀ x ∈ A₀, x ∉ A₁ := fun x hx hx' => hU x hx x hx' 0 (by simp) (by simp)
  let dd : Fin 2 → ℕ := ![r, t]
  let p : ∀ i, Irr k (dd i) := fun i =>
    Fin.cases (motive := fun i => Irr k (dd i)) π₁
      (fun j => Fin.cases (motive := fun j : Fin 1 => Irr k (dd j.succ)) π₂ (fun l => l.elim0) j) i
  let A : Fin 2 → Multiset (IrrGL (k := k)) := ![A₀, A₁]
  have hA : ∀ i, HasSupport (p i).π (A i) := by
    intro i
    fin_cases i
    · exact H₁
    · exact H₂
  have hd : ∑ i, dd i = dd 0 + dd 1 := Fin.sum_univ_two dd
  have hirr := isIrreducible_of_occurs hG hBZ p hA hAB (stdBlocks dd hd)
    (fun Q hQ => occurs hG hBZ hZ p hA hAB hU (stdBlocks dd hd) Q hQ)
  obtain ⟨E⟩ := GlobalTheory.LocGL.nonempty_prod₂_equiv_multiProd hd fun i => (p i).π
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv E.symm hirr

end GlobalTheory.CompanionTheory.Hypotheses₂.TDZ

theorem GlobalTheory.CompanionTheory.Hypotheses₂.totallyDisjointProductIrreducible_of_polynomialRing :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness →
      GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.TotallyDisjointProductIrreducible := by
  intro hG hBZ hZ k _ _ _ _ r t s s' π₁ π₂ d d' σ σ' h₁ h₂ hdis
  refine GlobalTheory.CompanionTheory.Hypotheses₂.TDZ.isIrreducible_prod₂ hG hBZ hZ π₁ π₂ (GlobalTheory.LocGL.hasSupport_of_isCuspSupport h₁)
    (GlobalTheory.LocGL.hasSupport_of_isCuspSupport h₂) ?_
  intro x hx y hy j hj heq
  obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hx
  obtain ⟨b, -, rfl⟩ := Multiset.mem_map.1 hy
  obtain ⟨hpq, hn⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_equiv_of_eq_nu (σ a) (σ' b) j heq
  exact hdis a b hpq j hj hn

theorem GlobalTheory.CompanionTheory.Hypotheses₂.totallyDisjointProductIrreducible_of_parts :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.SegmentRepresentation →
      GlobalTheory.Published.GrothendieckRingPolynomial → GlobalTheory.Published.TotallyDisjointProductIrreducible :=
  fun hG hS hP => GlobalTheory.CompanionTheory.Hypotheses₂.totallyDisjointProductIrreducible_of_polynomialRing hG
    GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
    (GlobalTheory.zelevinskyPolynomialRing_of_parts GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness hS hP)

end
end

