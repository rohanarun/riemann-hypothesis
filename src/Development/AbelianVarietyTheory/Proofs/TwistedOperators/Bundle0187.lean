module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0175

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleTensorComponentIdempotentSumAddConjEqOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adeleTensorComponent_idempotentSum_add_conj_eq_one : ∀ {D : D7} (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ PP ∈ Z, compFin D.host.F D.host.E ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) (e + cA D e) = 1 := by
  first | exact @GlobalTheory.CompFinIdemSum.compFin_add_cA_eq_one | exact GlobalTheory.CompFinIdemSum.compFin_add_cA_eq_one | (intros; apply GlobalTheory.CompFinIdemSum.compFin_add_cA_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharpolyUnitaryEqConjugateReciprocal
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TrEll

theorem charpoly_eq_sharp (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (hJ : J.det ≠ 0) (γ : GRat σ J) :
    γ.1.1.charpoly = sharp σ n γ.1.1.charpoly := by
  have h : (γ.1.1.map (σ : E →+* E))ᵀ * J * γ.1.1 = J := γ.2
  have hJu : IsUnit J := (Matrix.isUnit_iff_isUnit_det J).2 (Ne.isUnit hJ)
  obtain ⟨U, hU⟩ := hJu
  have hg : IsUnit γ.1.1 := γ.1.isUnit
  have hgd : IsUnit γ.1.1.det := (Matrix.isUnit_iff_isUnit_det _).1 hg
  have hJd : IsUnit J.det := Ne.isUnit hJ
  set g := γ.1.1 with hgdef
  have h2 : (g.map (σ : E →+* E))ᵀ = J * g⁻¹ * J⁻¹ := by
    have : (g.map (σ : E →+* E))ᵀ * J = J * g⁻¹ := by
      conv_rhs => rw [← h]
      rw [Matrix.mul_nonsing_inv_cancel_right _ _ hgd]
    rw [← this, Matrix.mul_nonsing_inv_cancel_right _ _ hJd]
  set c : E := (-1) ^ n * Ring.inverse g.det with hc
  have hc0 : c ≠ 0 := by
    rw [hc, Ring.inverse_eq_inv']
    exact mul_ne_zero (pow_ne_zero _ (by simp)) (inv_ne_zero hgd.ne_zero)
  have hdeg : g.charpoly.natDegree = n := by simp
  have h3 : g.charpoly.map (σ : E →+* E) = C c * reflect n g.charpoly := by
    rw [← Matrix.charpoly_map, ← Matrix.charpoly_transpose, h2, ← hU, Matrix.charpoly_units_conj,
      Matrix.charpoly_inv _ hg, ← Matrix.reverse_charpoly, Polynomial.reverse, hdeg, hc]
    simp
  have h4 : σ (g.charpoly.eval 0) = c := by
    have e : σ (g.charpoly.eval 0) = (g.charpoly.map (σ : E →+* E)).coeff 0 := by
      rw [coeff_map, coeff_zero_eq_eval_zero]; rfl
    have m : g.charpoly.coeff n = 1 := by
      have := (Matrix.charpoly_monic g).coeff_natDegree
      rwa [hdeg] at this
    rw [e, h3, coeff_C_mul, coeff_reflect, revAt_zero, m, mul_one]
  unfold sharp
  rw [h4, h3, reflect_C_mul, reflect_reflect, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc0, C_1, one_mul]

end GlobalTheory.TrEll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CmHostFractionalIdealPartitionOfUnity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HostAAPartition

theorem host_AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  have hb : D.host.𝔟 ≠ ⊥ := by
    intro h0
    have h1 := D.host.𝔟_spec.1
    rw [h0, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1
  have hc : D.host.ccE ≠ ⊥ := by
    unfold Formalism.BasicNotions.Host.ccE
    rw [Ne, Ideal.map_eq_bot_iff_of_injective
      (FaithfulSMul.algebraMap_injective (𝓞 D.host.K) (𝓞 D.host.E))]
    exact D.host.ccK_ne_bot
  unfold Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0
  exact mul_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hc)
    (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hb))

theorem host_AA_partition : ∀ (D : D7), ∃ (m : ℕ) (a c : Fin m → D.host.E), (∀ i, a i ∈ D.host.AA) ∧ (∀ i, ∀ x ∈ D.host.AA, ∃ b : 𝓞 D.host.E, (b : D.host.E) = c i * x) ∧ ∑ i, a i * c i = 1 := by
  intro D
  set I := D.host.AA with hI
  have hne : I ≠ 0 := host_AA_ne_zero D
  have h1 : (1 : D.host.E) ∈ I * I⁻¹ := by
    rw [mul_inv_cancel₀ hne]
    exact FractionalIdeal.one_mem_one _
  have key : ∀ z ∈ I * I⁻¹, ∃ (m : ℕ) (a c : Fin m → D.host.E), (∀ i, a i ∈ I) ∧
      (∀ i, ∀ x ∈ I, ∃ b : 𝓞 D.host.E, (b : D.host.E) = c i * x) ∧ ∑ i, a i * c i = z := by
    intro z hz
    refine FractionalIdeal.mul_induction_on (C := fun z => ∃ (m : ℕ) (a c : Fin m → D.host.E),
      (∀ i, a i ∈ I) ∧ (∀ i, ∀ x ∈ I, ∃ b : 𝓞 D.host.E, (b : D.host.E) = c i * x) ∧
        ∑ i, a i * c i = z) hz ?_ ?_
    · intro u hu v hv
      refine ⟨1, fun _ => u, fun _ => v, fun _ => hu, ?_, by simp⟩
      intro _ x hx
      have hvx : v * x ∈ I⁻¹ * I := FractionalIdeal.mul_mem_mul hv hx
      rw [inv_mul_cancel₀ hne, FractionalIdeal.mem_one_iff] at hvx
      obtain ⟨b, hb⟩ := hvx
      exact ⟨b, hb⟩
    · rintro u v ⟨m, a, c, ha, hc, rfl⟩ ⟨n, a', c', ha', hc', rfl⟩
      refine ⟨m + n, Fin.append a a', Fin.append c c', ?_, ?_, ?_⟩
      · intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa using ha j
        · simpa using ha' j
      · intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa using hc j
        · simpa using hc' j
      · rw [Fin.sum_univ_add]
        simp
  exact key 1 h1

end GlobalTheory.HostAAPartition
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjFormsSpherical
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjSph

open GlobalTheory.Hk3

variable {D : D7} {V : HSp D} {P : Pl D.host.E}

theorem adForms_iff {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ι : Γ →* G)
    (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (F : G → W) :
    F ∈ Bridge.AdForms ι ρ J χ ↔
      (∀ h (k : J), F (h * k) = ((χ k : ℂˣ) : ℂ) • F h) ∧ ∀ γ h, F (ι γ * h) = ρ γ (F h) := by
  change (∀ (γ : Γ) (h : G) (k : J), F (ι γ * h * k) = ((χ k : ℂˣ) : ℂ) • ρ γ (F h)) ↔ _
  constructor
  · intro hF
    refine ⟨fun h k => ?_, fun γ h => ?_⟩
    · simpa using hF 1 h k
    · simpa using hF γ h 1
  · rintro ⟨hR, hL⟩ γ h k
    rw [hR, hL]

def hkG {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (φ : GA D V →* G) (P : Pl D.host.E) (c : List ℤ →₀ ℂ)
    (F : G → W) : G → W :=
  fun h => c.sum fun d z => z • ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (h * φ γ)

theorem dual_hkG {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (φ : GA D V →* G) (l : W →ₗ[ℂ] ℂ) (c : List ℤ →₀ ℂ)
    (F : G → W) (x : GA D V) : l (hkG φ P c F (φ x)) = hk V P c (fun y => l (F (φ y))) x := by
  rw [GlobalTheory.LevOp.hk_apply]
  show l (c.sum fun d z => z • ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (φ x * φ γ)) = _
  rw [map_finsuppSum, Finsupp.sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_smul, map_sum, smul_eq_mul]
  congr 1
  show _ = ∑ γ ∈ GlobalTheory.Hk3.rep V P d, l (F (φ (x * γ)))
  simp only [map_mul]

theorem hkG_left {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (φ : GA D V →* G) (c : List ℤ →₀ ℂ)
    (F : G → W) (g : G) (T : W →ₗ[ℂ] W) (hF : ∀ h, F (g * h) = T (F h)) (h : G) :
    hkG φ P c F (g * h) = T (hkG φ P c F h) := by
  show (c.sum fun d z => z • ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (g * h * φ γ)) =
    T (c.sum fun d z => z • ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (h * φ γ))
  rw [map_finsuppSum]
  refine Finsupp.sum_congr fun d _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [mul_assoc, hF]

theorem hkG_right {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (φ : GA D V →* G) (hφ : Function.Surjective φ)
    {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {J : Subgroup (GA D V)}
    (hJ : ∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅)) (c : List ℤ →₀ ℂ) (F : G → W)
    (hF : ∀ k ∈ GlobalTheory.Hk3.hyp V P, ∀ h, F (h * φ k) = F h) {k₁ k₂ : GA D V} (hk₁ : k₁ ∈ J)
    (s₁ : SuppF V f k₁) (s₂ : SuppF V (1 - f) k₂) (z : ℂ) (hz : ∀ h, F (h * φ (k₁ * k₂)) = z • F h) (h : G) :
    hkG φ P c F (h * φ (k₁ * k₂)) = z • hkG φ P c F h := by
  obtain ⟨x, rfl⟩ := hφ h
  rw [← map_mul φ x (k₁ * k₂), ← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  rw [map_sub, map_smul, dual_hkG, dual_hkG, sub_eq_zero, smul_eq_mul]
  have hinv : ∀ k ∈ GlobalTheory.Hk3.hyp V P, ∀ y, (fun y => l (F (φ y))) (y * k) = (fun y => l (F (φ y))) y := by
    intro k hk y
    show l (F (φ (y * k))) = l (F (φ y))
    rw [map_mul, hF k hk]
  rw [GlobalTheory.LevOp.hk_translate hP hJ c hinv hk₁ s₁ s₂ x]
  have hsc : (fun y => (fun y => l (F (φ y))) (y * (k₁ * k₂))) = z • fun y => l (F (φ y)) := by
    funext y
    show l (F (φ (y * (k₁ * k₂)))) = z * l (F (φ y))
    rw [map_mul φ y (k₁ * k₂), hz, map_smul, smul_eq_mul]
  rw [hsc, map_smul]
  rfl


set_option maxHeartbeats 1000000 in
theorem adForms_spherical (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ)
    (L : LevDat D.host.E ℂ V.rank) (hB : IsBaseFrame V β Λ N) (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hPP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P)
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ρ : GQ V →* Module.End ℂ W)
    (χ' : (levEnv V β L).J →* ℂˣ) (hχ' : ∀ k, (((levEnv V β L).χ k : ℂˣ) : ℂ) = 1 → ((χ' k : ℂˣ) : ℂ) = 1)
    {F : Bridge.Gf V → W} (hF : F ∈ Bridge.AdForms (Bridge.ratF V) ρ (levEnv V β L).J χ') (c : List ℤ →₀ ℂ) :
    (∀ k ∈ GlobalTheory.Hk3.hyp V P, ∀ h, F (h * (finHom V).rangeRestrict k) = F h) ∧
      hkF V P c F ∈ Bridge.AdForms (Bridge.ratF V) ρ (levEnv V β L).J χ' := by
  obtain ⟨e, f, hP⟩ := (_root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.1 P
  have hPf := (_root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e f hP
  obtain ⟨hJf, hχf, hsplit⟩ := (GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places V β Λ N (flag1L L) hB).2 P e f hP hN hPP
  have hFl := (adForms_iff (Bridge.ratF V) ρ (levEnv V β L).J χ' F).1 hF
  have hinv : ∀ k ∈ GlobalTheory.Hk3.hyp V P, ∀ h, F (h * (finHom V).rangeRestrict k) = F h := by
    rintro k ⟨hkK, e', f', hP', hk⟩ h
    obtain ⟨-, rfl⟩ := hPf.2.2.2.1 e' f' hP'
    have hkJ : k ∈ levG V β (flag1L L) := (hJf k hk).2 hkK
    have hmem : (finHom V).rangeRestrict k ∈ (levEnv V β L).J :=
      (GlobalTheory.SplitHeckeAdj.mem_J V β L (hPf.2.2.1 k hk)).2 hkJ
    have h1 : (((levEnv V β L).χ ⟨_, hmem⟩ : ℂˣ) : ℂ) = 1 := by
      rw [GlobalTheory.SplitHeckeAdj.chi_eq V β L hmem]
      exact hχf k hkJ hk
    rw [hFl.1 h ⟨_, hmem⟩, hχ' _ h1, one_smul]
  refine ⟨hinv, (adForms_iff (Bridge.ratF V) ρ (levEnv V β L).J χ' _).2 ⟨fun h k => ?_, fun γ h => ?_⟩⟩
  · obtain ⟨g, hgG, hg⟩ := GlobalTheory.SplitHeckeAdj.fin_lift V (k : Bridge.Gf V)
    have hgJ : g ∈ levG V β (flag1L L) := by
      refine (GlobalTheory.SplitHeckeAdj.mem_J V β L hgG).1 ?_
      rw [hg]
      exact k.2
    obtain ⟨k₁, hk₁, k₂, -, s₁, s₂, rfl⟩ := hsplit g hgJ
    have hz : ∀ h', F (h' * (finHom V).rangeRestrict (k₁ * k₂)) = ((χ' k : ℂˣ) : ℂ) • F h' := by
      intro h'
      rw [show (finHom V).rangeRestrict (k₁ * k₂) = (k : Bridge.Gf V) from hg]
      exact hFl.1 h' k
    have key := hkG_right (P := P) (finHom V).rangeRestrict (MonoidHom.rangeRestrict_surjective _) hP
      (J := levG V β (flag1L L)) hJf c F hinv hk₁ s₁ s₂ _ hz h
    rw [show (finHom V).rangeRestrict (k₁ * k₂) = (k : Bridge.Gf V) from hg] at key
    exact key
  · exact hkG_left (P := P) (finHom V).rangeRestrict c F (Bridge.ratF V γ) (ρ γ) (hFl.2 γ) h


set_option maxHeartbeats 1000000 in
theorem conjForms_spherical : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), ∀ c₀, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ c₀ c c₁ H j → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → ∀ cV (y : H.H), (∀ k ∈ GlobalTheory.Hk3.hyp (Vc D i) P, ∀ h, H.e y (h * (finHom _).rangeRestrict k) = H.e y h) ∧ ∃ y' : H.H, H.e y' = GlobalTheory.Hk3.hkF (Vc D i) P cV (H.e y) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hR i σ c c₁ H j c₀ hC P hG cV y
  obtain ⟨χ', hχc, hIs⟩ := hC.model
  obtain ⟨-, hrange, -⟩ := hIs
  have hSD : ∃ c, IsBaseFrame (Vc D i) (R.βV i) (R.ΛV i) (1 ^ c) := hR.βV i
  obtain ⟨n, hB⟩ := hSD
  have hN : (((1 ^ n : ℕ) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have htriv : ∀ k, (((levEnv (Vc D i) (R.βV i) (R.datVt i A.μ0)).χ k : ℂˣ) : ℂ) = 1 → ((χ' k : ℂˣ) : ℂ) = 1 := by
    intro k hk
    obtain ⟨a, ha, hb⟩ := hχc k
    have ha1 : a = 1 := D.what₂.embLL.injective (by rw [ha, hk, map_one])
    rw [← hb, ha1, map_one]
  have hPP : ∀ PP, PP ∈ (R.datVt i A.μ0).Pg ∨ PP ∈ (R.datVt i A.μ0).Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := hG
  have key := adForms_spherical (V := Vc D i) (P := P) (R.βV i) (R.ΛV i) (1 ^ n) (R.datVt i A.μ0) hB hN hPP c.coef.ρ χ' htriv (F := H.e y) (by
      have h0 := LinearMap.mem_range_self H.e y
      rw [hrange] at h0
      exact h0) cV
  have k1 : ∀ k ∈ GlobalTheory.Hk3.hyp (Vc D i) P, ∀ h, H.e y (h * (finHom (Vc D i)).rangeRestrict k) = H.e y h := by
    intro k hk h
    exact key.1 k hk h
  refine ⟨fun k hk h => Eq.trans ?_ (k1 k hk h), ?_⟩
  · congr! 2
  have h3 : GlobalTheory.Hk3.hkF (Vc D i) P cV (H.e y) ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (levJ R i A.μ0) χ' := key.2
  have h4 : GlobalTheory.Hk3.hkF (Vc D i) P cV (H.e y) ∈ LinearMap.range H.e := (SetLike.ext_iff.mp hrange _).mpr h3
  obtain ⟨y', hy'⟩ := h4
  exact ⟨y', hy'⟩

end GlobalTheory.ConjSph

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffProdLinearMapUpperRightLowerRightBlocksStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_prodLinearMap_upperRight_lowerRight_blocks : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (J : ℝ → (V × V) →ₗ[ℝ] (V × V)), (∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => J t w) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockB (J t)) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockD (J t)) := by
  first | exact @GlobalTheory.FockFamily.contDiff_blockB_blockD | exact GlobalTheory.FockFamily.contDiff_blockB_blockD | (intros; apply GlobalTheory.FockFamily.contDiff_blockB_blockD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMeanSquareNormWeilRepSub
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilNormCont

theorem continuous_meanSquareNorm_weilRep_sub : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsCovolOne (ratL T S) μ 𝓕 → ∀ f₁ f₂ : WO S T → ℂ, IsThetaFunO ψ S T f₁ → IsThetaFunO ψ S T f₂ → Continuous fun p : GA D S × GA D T => nrm2 μ 𝓕 (om p f₁ - f₂) := by
  intro D ψ S T χS χT om μ 𝓕 hom hμ f₁ f₂ h₁ h₂
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  obtain ⟨b, hb⟩ := GlobalTheory.WeilSupBound.exists_sup_bound D ψ S T χS χT om hom f₂ h₂ {1} isCompact_singleton
  have hb' : ∀ w, ‖f₂ w‖ ≤ b := fun w => by simpa using hb 1 rfl w
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds p₀
  obtain ⟨c, hc⟩ := GlobalTheory.WeilSupBound.exists_sup_bound D ψ S T χS χT om hom f₁ h₁ K hK
  unfold nrm2
  refine continuousAt_of_dominated (bound := fun _ => (c + b) ^ 2) ?_ ?_ (integrable_const _) ?_
  · refine Filter.Eventually.of_forall fun p => ?_
    exact ((((hom.om_pres p f₁ h₁).cont.sub h₂.cont).norm.pow 2).measurable).aestronglyMeasurable
  · filter_upwards [hK0] with p hp
    refine Filter.Eventually.of_forall fun w => ?_
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (add_le_add (hc p hp w) (hb' w))) 2
  · refine Filter.Eventually.of_forall fun w => ?_
    exact (((hom.om_cont f₁ h₁ w).sub continuous_const).norm.pow 2).continuousAt

end GlobalTheory.WeilNormCont
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoordEquivApply
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrUnitLat

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)

def powB : Module.Basis (Fin r) E (Fld P) :=
  (AdjoinRoot.powerBasis P.2.2.1.ne_zero).basis.reindex
    (finCongr ((AdjoinRoot.powerBasis_dim P.2.2.1.ne_zero).trans P.2.2.2.1))

def gramOne : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun i j => Algebra.trace E (Fld P) (powB P j * star' P (powB P i))

variable (k : Type) [CommRing k] [Algebra F k]

def coordF (i : Fin r) : k ⊗[F] Fld P →ₗ[F] k ⊗[F] E :=
  LinearMap.lTensor k (((powB P).coord i).restrictScalars F)

theorem coordF_tmul (i : Fin r) (a : k) (z : Fld P) : coordF P k i (a ⊗ₜ[F] z) = a ⊗ₜ[F] (powB P).repr z i := rfl

theorem smul_eq_map_mul (c : k ⊗[F] E) (y : k ⊗[F] Fld P) :
    c • y = Algebra.TensorProduct.map (AlgHom.id F k) (IsScalarTower.toAlgHom F E (Fld P)) c * y :=
  Algebra.smul_def c y

theorem coordF_smul (i : Fin r) (c : k ⊗[F] E) (y : k ⊗[F] Fld P) : coordF P k i (c • y) = c * coordF P k i y := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add c c' h h' => rw [add_smul, map_add (f := _), h, h', add_mul]
  | tmul a e =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' h h' => rw [smul_add, map_add (f := _), h, h', map_add (f := _), mul_add]
    | tmul a' z =>
      rw [smul_eq_map_mul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, coordF_tmul,
        coordF_tmul, Algebra.TensorProduct.tmul_mul_tmul]
      congr 1
      change (powB P).repr (algebraMap E (Fld P) e * z) i = e * _
      rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]

def coordInv (w : Fin r → k ⊗[F] E) : k ⊗[F] Fld P := ∑ i, w i • ((1 : k) ⊗ₜ[F] powB P i)

theorem coordF_coordInv (w : Fin r → k ⊗[F] E) (j : Fin r) : coordF P k j (coordInv P k w) = w j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coordInv, map_sum, coordF_smul, coordF_tmul, Module.Basis.repr_self]
  rw [Finset.sum_eq_single j (fun i _ h => by rw [Finsupp.single_apply, if_neg h, TensorProduct.tmul_zero, mul_zero])
    (by simp), Finsupp.single_eq_same, ← Algebra.TensorProduct.one_def, mul_one]

theorem coordInv_coordF (y : k ⊗[F] Fld P) : coordInv P k (fun i => coordF P k i y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp [coordInv]
  | add y y' h h' =>
    conv_rhs => rw [← h, ← h']
    simp only [coordInv, map_add (f := _), add_smul, Finset.sum_add_distrib]
  | tmul a z =>
    simp only [coordInv, coordF_tmul, smul_eq_map_mul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, AlgHom.id_apply, IsScalarTower.coe_toAlgHom']
    rw [← TensorProduct.tmul_sum]
    congr 1
    conv_rhs => rw [← (powB P).sum_repr z]
    exact Finset.sum_congr rfl fun i _ => (Algebra.smul_def _ _).symm

def coordEquiv : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E) where
  toFun y i := coordF P k i y
  map_add' y y' := funext fun i => map_add _ _ _
  map_smul' c y := funext fun i => coordF_smul P k i c y
  invFun := coordInv P k
  left_inv y := coordInv_coordF P k y
  right_inv w := funext fun j => coordF_coordInv P k w j

theorem coordEquiv_apply (y : k ⊗[F] Fld P) (i : Fin r) : coordEquiv P k y i = coordF P k i y := rfl

end GlobalTheory.TrUnitLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqExpFockGaussianFormOfHeisenbergDerivativeEqStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_exp_fockGaussianForm_of_heisenbergDerivative_eq : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (J : (V × V) →ₗ[ℝ] (V × V)), IsUnit (GlobalTheory.FockFamily.blockB J) → ∀ g : V → ℂ, Differentiable ℝ g →
    (∀ w x, GlobalTheory.GaussLine.dHeis β (J w) g x = Complex.I * GlobalTheory.GaussLine.dHeis β w g x) →
    ∀ x, g x = g 0 * Complex.exp (GlobalTheory.FockFamily.fockForm β J x x) := by
  first | exact @GlobalTheory.FockFamily.solution_eq_gauss | exact GlobalTheory.FockFamily.solution_eq_gauss | (intros; apply GlobalTheory.FockFamily.solution_eq_gauss <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialIsoUnitaryPairStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fockPolynomialIso_unitaryPair : ∀ (p q r s a b : ℕ) (ε : Fin a → Bool) (ε' : Fin b → Bool) (e : Ix p q ≃ Fin a) (e' : Ix r s ≃ Fin b), GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat ε e → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat ε' e' → ∃ κ : LPol b a ≃ₗ[ℂ] Pol p q r s, IsPolyIso ε ε' e e' κ := by
  first | exact @GlobalTheory.Chain.RealIt.PolyIso.exists_isPolyIso | exact GlobalTheory.Chain.RealIt.PolyIso.exists_isPolyIso | (intros; apply GlobalTheory.Chain.RealIt.PolyIso.exists_isPolyIso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGlobalFockIntertwinerTensorRealPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_globalFockIntertwiner_tensor_realPlaces : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (aS aT : D.what₂.Tau → ℚ) (A : ∀ τ, LPol W.rank V.rank →ₗ[ℂ] M'.H τ →ₗ[ℂ] M.H τ), GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels.ContrTensor → GlueLaw D V.rank W.rank → (∀ τ, LocIt M M' τ (aS τ) (aT τ) (A τ)) → ∃ It I, GlobIt M M' aS aT It I := by
  first | exact @GlobalTheory.Chain.RealIt.TensorGlob.exists_globIt | exact GlobalTheory.Chain.RealIt.TensorGlob.exists_globIt | (intros; apply GlobalTheory.Chain.RealIt.TensorGlob.exists_globIt <;> assumption)
end

