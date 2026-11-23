module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0765
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0764
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Formalism.LocalToGlobal.ProjectiveLattices.UnifDom
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0767
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefMapSmulMap
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CoefLin

open MvPolynomial Formalism.L2.Pj

variable {σ : Type} (F : IntermediateField ℚ ℂ) (lam : ℂ →ₗ[F] F)

def coefFun (p : MvPolynomial σ ℂ) : MvPolynomial σ F := ∑ m ∈ p.support, monomial m (lam (p.coeff m))

theorem coeff_coefFun (p : MvPolynomial σ ℂ) (m : σ →₀ ℕ) : (coefFun F lam p).coeff m = lam (p.coeff m) := by
  classical
  rw [coefFun, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, map_zero]

def coefMap : MvPolynomial σ ℂ →+ MvPolynomial σ F where
  toFun := coefFun F lam
  map_zero' := by
    ext m
    simp only [coeff_coefFun, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, map_zero]
  map_add' p q := by
    ext m
    simp only [coeff_coefFun, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add]

variable {F lam}

theorem coeff_coefMap (p : MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    (coefMap F lam p).coeff m = lam (p.coeff m) :=
  coeff_coefFun F lam p m

theorem coefMap_monomial (m : σ →₀ ℕ) (c : ℂ) :
    coefMap F lam (monomial m c) = lam c • monomial m (1 : F) := by
  ext m'
  rw [coeff_coefMap, coeff_smul, coeff_monomial, coeff_monomial]
  split_ifs <;> simp

theorem coefMap_smul_map (c : ℂ) (R : MvPolynomial σ F) :
    coefMap F lam (c • map (algebraMap F ℂ) R) = lam c • R := by
  ext m
  rw [coeff_coefMap, coeff_smul, coeff_map, coeff_smul, smul_eq_mul, smul_eq_mul]
  have : c * algebraMap F ℂ (R.coeff m) = R.coeff m • c := by
    rw [Algebra.smul_def, mul_comm]
  rw [this, map_smul, smul_eq_mul, mul_comm]

theorem coefMap_comm (Φ : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ) (Ψ : MvPolynomial σ F →ₗ[F] MvPolynomial σ F)
    (h : ∀ Q, Φ (map (algebraMap F ℂ) Q) = map (algebraMap F ℂ) (Ψ Q)) (p : MvPolynomial σ ℂ) :
    coefMap F lam (Φ p) = Ψ (coefMap F lam p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial m c =>
    have hm : (monomial m c : MvPolynomial σ ℂ) = c • map (algebraMap F ℂ) (monomial m (1 : F)) := by
      rw [map_monomial, map_one, smul_monomial, smul_eq_mul, mul_one]
    rw [hm, map_smul, h, coefMap_smul_map, ← hm, coefMap_monomial, map_smul]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), map_add (f := _)]

variable {T : Type} (r : T → ℕ) (n : ℕ)

theorem lap_map (τ τ' : T) (a : Fin (r τ)) (a' : Fin (r τ')) (Q : MvPolynomial (Letter T r n) F) :
    lap r n ℂ 1 τ τ' a a' (map (algebraMap F ℂ) Q) = map (algebraMap F ℂ) (lap r n F 1 τ τ' a a' Q) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lap, LinearMap.sum_apply, map_sum, LinearMap.smul_apply]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp [pderiv_map]

theorem rowShift_map (σ₀ : T) (i i' : Fin (r σ₀)) (t : F) (Q : MvPolynomial (Letter T r n) F) :
    rowShift r n ℂ σ₀ i i' (t : ℂ) (map (algebraMap F ℂ) Q) = map (algebraMap F ℂ) (rowShift r n F σ₀ i i' t Q) := by
  have key : (rowShift r n ℂ σ₀ i i' (t : ℂ)).toRingHom.comp (map (algebraMap F ℂ)) =
      (map (algebraMap F ℂ)).comp (rowShift r n F σ₀ i i' t).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp [rowShift]
    · intro ℓ
      simp only [rowShift, RingHom.coe_comp, Function.comp_apply, map_X, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, aeval_X]
      split_ifs <;> simp
  exact RingHom.congr_fun key Q

end GlobalTheory.CoefLin

namespace GlobalTheory.SingleDatum

open MvPolynomial Formalism.L2.Pj GlobalTheory.CoefLin

theorem HHa_coefLin : ∀ (T : Type) (r : T → ℕ) (n : ℕ) (cj : T → T) (isX : T → Prop) (a : T → ℕ → ℕ)
    (F : IntermediateField ℚ ℂ) (lam : ℂ →ₗ[F] F), ∀ P ∈ HHa r n ℂ cj isX a, ∃ P' ∈ HHa r n F cj isX a,
      ∀ mo, P'.coeff mo = lam (P.coeff mo) := by
  intro T r n cj isX a F lam P hP
  obtain ⟨hH, hR, hD⟩ := hP
  refine ⟨coefMap F lam P, ⟨?_, ?_, ?_⟩, coeff_coefMap P⟩
  · simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at hH ⊢
    intro τ hτ i i'
    rw [← coefMap_comm (lap r n ℂ 1 τ (cj τ) i i') (lap r n F 1 τ (cj τ) i i') (lap_map r n τ (cj τ) i i') P,
      hH τ hτ i i', map_zero]
  · intro σ₀ i i' hii t
    have key := coefMap_comm (lam := lam) (rowShift r n ℂ σ₀ i i' (t : ℂ)).toLinearMap
      (rowShift r n F σ₀ i i' t).toLinearMap (rowShift_map r n σ₀ i i' t) P
    simp only [AlgHom.toLinearMap_apply] at key
    rw [← key, hR σ₀ i i' hii (t : ℂ)]
  · intro m hm σ₀ i
    refine hD m ?_ σ₀ i
    rw [mem_support_iff] at hm ⊢
    intro h0
    apply hm
    rw [coeff_coefMap, h0, map_zero]

end GlobalTheory.SingleDatum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverSectionsLinearIndependentAdelicReadings
section
noncomputable section

namespace GlobalTheory.CoverIndep

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Matrix
open GlobalTheory.ShortMove GlobalTheory.ShortMoveIso GlobalTheory.TwistTie

theorem rmul_mem_bor {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} {b b' : Frame Ψ r}
    (hb : b ∈ Bor Ψ r) (hb' : b' ∈ Bor Ψ r) : rmul b b' ∈ Bor Ψ r := by
  intro τ
  have ht : (mat b τ).BlockTriangular id := fun a c h => (hb τ).2 a c h
  have ht' : (mat b' τ).BlockTriangular id := fun a c h => (hb' τ).2 a c h
  refine ⟨?_, fun a c h => (ht.mul ht') h⟩
  show (mat b τ * mat b' τ).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero (hb τ).1 (hb' τ).1

theorem rmul_lact_rmul {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (γ : GL (Fin r) E) (x b b' : Frame Ψ r) :
    rmul (lact γ (rmul x b)) b' = rmul (lact γ x) (rmul b b') := by
  funext τ
  show ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ)) * mat b' τ =
    ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) * (mat b τ * mat b' τ)
  simp only [Matrix.mul_assoc]


set_option maxHeartbeats 1000000 in
theorem dict_onto {D : D7} (V : HSp D) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (hr : V.rank = r)
    (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hσ : GoodEmb c σ) (hA : l.A = 1) (hpq : 1 ≤ Dw.p + Dw.q)
    (hU : IsUnf U) (hW : ∀ k, ModelW V hr (U.X k)) (hD : DictLat U V hr dict io e F ik φ th x₀)
    (hι : GlobalTheory.Member.IotaOK Dw V io) (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ))
    (hx : ∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 →
      gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) (x₀ τ) =
        Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ))
    (hdom : ∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) (k : U.Comp) (x : Frame (U.X k).Ψ r) (hxd : x ∈ (U.X k).dom) :
    ∃ h, ∃ γ ∈ (U.X k).Γ, ∃ b ∈ Bor (U.X k).Ψ r, dict h = ⟨k, rmul (lact γ x) b⟩ := by
  subst hr
  have hx₀ : ∀ k, IsOrthogonalFrame (U.X k) x₀ := fun k τ hτ => by
    rw [(hW k).1, (hU.2.1 k).1]
    exact hx τ (((hU.2.1 k).2 τ).1 hτ)
  obtain ⟨h1, h4⟩ := GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal D.host.E V.rank (U.X k).p0
    (U.X k).Ψ (U.X k).Gm (U.X k).Gm_herm
  obtain ⟨x₁, b, hb, ho, hx₁⟩ := h1 x hxd
  have hx₁d : x₁ ∈ (U.X k).dom := ((GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular D.host.E V.rank (U.X k).p0
    (U.X k).Ψ (U.X k).Gm (U.X k).Gm_herm).2.1 x₁ ho).1
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  obtain ⟨hAr, -, hL⟩ := _root_.GlobalTheory.Member.Arch.archM_spec D V θ hθ
  have hG : ∀ k, (U.X k).Gm = -V.gramᵀ := fun k => (hW k).1
  have hmem : ∀ k (τ : D.host.E →+* ℂ), τ ∈ (U.X k).Ψ ↔ τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD := by
    intro k τ
    rw [(hU.2.1 k).2 τ, hι.rt, hι.rt0]
  have hex : ∀ τ : D.host.E →+* ℂ, ∃ u : Matrix (Fin V.rank) (Fin V.rank) ℂ, ∀ hτ : τ ∈ (U.X k).Ψ,
      uᵀ * (-V.gramᵀ).map τ * u.map (starRingEnd ℂ) = (-V.gramᵀ).map τ ∧ mat x₁ ⟨τ, hτ⟩ = u * x₀ τ := by
    intro τ
    by_cases hτ : τ ∈ (U.X k).Ψ
    · obtain ⟨u, hu⟩ := h4 τ (x₀ τ) (mat x₁ ⟨τ, hτ⟩) (hx₀ k τ hτ) ((ho ⟨τ, hτ⟩).trans (hx₀ k τ hτ).symm)
      rw [hG] at hu
      exact ⟨u, fun _ => hu⟩
    · exact ⟨1, fun h' => absurd h' hτ⟩
  choose u hu using hex
  obtain ⟨a, ha, hau⟩ := hL u fun τ hτ => (hu τ ((hmem k τ).2 hτ)).1
  have hty := (GlobalTheory.Relab.relab_good _ H l c σ hσ).2.2.2 Dw g e
  obtain ⟨h₀, hh₀⟩ := GlobalTheory.ShortMove.exists_marked_of_component D V H Dw l Xo _ g _ F hty _ rfl (U.X k) (ik k) (φ k) io
    (hW k) (hD.1.1 k) hι.emb hι.isom
  obtain ⟨a₀, ha₀, f, hf, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 h₀
  have hfin : finHom V (a₀ * f) = finHom V (a * f) := by
    rw [map_mul, map_mul, show finHom V a₀ = 1 from ha₀, show finHom V a = 1 from ha]
  have hh : Marked V rfl io l (U.X k).Λ (fun a => (φ k (F.t (ik k) a) : Fin V.rank → D.host.E)) (a * f) := by
    obtain ⟨e₁, e₂⟩ := (_root_.GlobalTheory.Member.latG_move D V).2.1 _ _ hfin
    unfold Marked at hh₀ ⊢
    rwa [e₁, e₂, hfin] at hh₀
  refine ⟨a * f, ?_⟩
  obtain ⟨γ, hγ, hΛ, hm, hfr⟩ := hD.2 (a * f)
  obtain ⟨δ, hδu, hδf, hδa⟩ := GlobalTheory.MarkCoset.rational_matrix V γ hγ
  obtain ⟨gam, e₁, t₁, hgam⟩ := marked_isometry_half V l io (U.X k) (U.X (dict (a * f)).1) _ _ (φ k) (φ _) (F.t _) (F.t _)
    LinearMap.id (a * f) γ 1 (hW k) (hW _) (hD.1.1 k) (hD.1.1 _) δ hδu hδf rfl (fun a _ => ⟨0, zero_mem _, by
      rw [map_one, Units.val_one, Matrix.one_mulVec, smul_zero, add_zero]; rfl⟩) hh
    (by rw [mul_one]; exact ⟨hΛ, hm⟩)
  obtain ⟨P, hPe, hP, hy, hd⟩ := hD.1.2 k ⟨x₁, hx₁d⟩
  obtain ⟨P', hPe', hP', hy', hd'⟩ := hD.1.2 (dict (a * f)).1 ⟨_, hdom _⟩
  obtain ⟨γ', hγ', b', hb', hk⟩ := (hU.2.2.2.1 k (dict (a * f)).1 ⟨x₁, hx₁d⟩ ⟨_, hdom _⟩).1
    (GlobalTheory.CoverOnto.frBor_of_isometry e F hpq hσ hA gam e₁ t₁ hP hP' (fun v => funext fun j => by
      rw [hPe, hPe', hgam]
      refine perFr_of_unitary _ _ (fun τ => by rw [hmem, hmem]) (by rw [hG, hG])
        (by rw [(hU.2.1 _).1, (hU.2.1 _).1]) (by rw [hG]; exact hδu) (fun τ h h' => ?_) _ _ _
      rw [hfr ⟨τ, h'⟩, GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth _ ⟨τ, h'⟩) (hθ τ), (hAr τ).2.1, (hAr τ).2.1,
        (hAr τ).2.2.1 f hf, hδa τ _ (hθ τ), hau τ ((hmem k τ).1 h), (hu τ h).2, Matrix.mul_one, ← Matrix.mul_assoc]
      rfl) _ _ hy hy' hd hd')
  refine ⟨γ', hγ', rmul b b', rmul_mem_bor hb hb', ?_⟩
  rw [← rmul_lact_rmul, ← hx₁]
  exact hk

theorem bchar_ne_zero' {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ}
    (la : Wt Ψ r) {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) : bchar la b ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ ?_
  have ht : (mat b τ).BlockTriangular id := fun a c h => (hb τ).2 a c h
  have hd := (hb τ).1
  rw [Matrix.det_of_upperTriangular ht] at hd
  exact Finset.prod_ne_zero_iff.1 hd i (Finset.mem_univ _)

theorem indep_along {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp G : Type}
    (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r) (dict : G → Σ k, Frame (X k).Ψ r)
    (honto : ∀ k, ∀ x ∈ (X k).dom, ∃ g, ∃ γ ∈ (X k).Γ, ∃ b ∈ Bor (X k).Ψ r, dict g = ⟨k, rmul (lact γ x) b⟩)
    (ν : G → ℂ) (hν : ∀ g, ν g ≠ 0)
    {m : ℕ} (P : Fin m → FDSec X) (hS : ∀ i k, (X k).IsSec (la k) (P i k)) (h0 : ∀ i, P i ∈ offZero X)
    (hP : LinearIndependent ℂ P) (φ : Fin m → G → ℂ) (hφ : ∀ i g, φ i g = ν g * P i (dict g).1 (dict g).2) :
    LinearIndependent ℂ φ := by
  rw [Fintype.linearIndependent_iff] at hP ⊢
  intro c hc
  refine hP c ?_
  funext k x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  by_cases hx : x ∈ (X k).dom
  · obtain ⟨g, γ, hγ, b, hb, hg⟩ := honto k x hx
    have h := congrFun hc g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hφ] at h
    have hγx : lact γ x ∈ (X k).dom := dom_lact (X k) hx ((X k).Γ_stab γ hγ)
    have hχ : (X k).χ (la k) γ ≠ 0 := by
      obtain ⟨N, hN, hN1⟩ := (X k).χ_fin (la k)
      intro h0'
      have := hN1 γ hγ
      rw [h0', zero_pow hN.ne'] at this
      exact zero_ne_one this
    have e : ∀ i, P i (dict g).1 (dict g).2 = bchar (la k) b * (X k).χ (la k) γ * P i k x := by
      intro i
      rw [hg]
      show P i k (rmul (lact γ x) b) = _
      rw [(hS i k).2.1 _ hγx b hb, (hS i k).2.2 γ hγ x hx, mul_assoc]
    have hne := mul_ne_zero (hν g) (mul_ne_zero (bchar_ne_zero' (la k) hb) hχ)
    have key : ν g * (bchar (la k) b * (X k).χ (la k) γ) * ∑ i, c i * P i k x =
        ∑ i, c i * (ν g * P i (dict g).1 (dict g).2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [e i]; ring
    rw [h] at key
    exact (mul_eq_zero.1 key).resolve_left hne
  · exact Finset.sum_eq_zero fun i _ => by rw [h0 i k x hx, mul_zero]


open GlobalTheory.CoverRead GlobalTheory.Member in
set_option maxHeartbeats 1000000 in
theorem cover_rd_linearIndependent : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → CUnit C.cc₂ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ (m : ℕ) (f : Fin m → Rul C.d.Xo₂ C.d.c₂), (∀ i, f i ∈ sec C.d.Xo₂ C.d.c₂ a n) → LinearIndependent C.d.c₂.F f → LinearIndependent ℂ (fun i => C.rd a (f i)) := by
  intro D T hT j hj σ hσ C hC hcc a n hdn m f hf hind
  obtain ⟨-, hA, hinc, hU, hdom, hr, g, e, F, ik, φ, th, hW, hth, hD⟩ := hC
  obtain ⟨hio, hx₀⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T hT j hj σ hσ _ rfl hr
  have hpq := (exists_iotaOK D T.Q hT.pins _ hj).2
  have hσ₂ : GoodEmb C.d.c₂ C.σ₂ := by
    rw [← hinc] at hσ
    exact hσ
  have hI : LinearIndependent ℂ (fun i => rdU C.U₂ (f i)) :=
    (GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.abelianSchemeLaws_all.1.secBaseChange _ _ _ _ _ _ _ _
      (Formalism.L2.PjFree.Unf.ofPj C.U₂) hU a n).1 m f hf hind
  have hl : ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (lieFac_pos _ _ _).ne'
  refine indep_along C.U₂.X (laU C.U₂ a n) C.dict₂
    (fun k x hx => dict_onto (T.V j σ) hr C.U₂ C.dict₂ _ e F ik φ th _ hσ₂ hA (by omega) hU hW hD hio hth hx₀ hdom
      k x hx)
    (fun g => ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) * (C.cc₂ (C.dict₂ g).1 * T.mu j σ g)) ?_
    (fun i => rdU C.U₂ (f i)) (fun i k => hU.2.2.2.2.1 a n hdn _ (hf i) k)
    (fun i => rdU_mem_offZero _ _) hI _ ?_
  · intro g
    refine mul_ne_zero hl (mul_ne_zero ?_ ?_)
    · exact norm_ne_zero_iff.1 (by rw [hcc]; exact one_ne_zero)
    · exact norm_ne_zero_iff.1 (by rw [(hT.muVal j hj σ hσ).norm g]; exact one_ne_zero)
  · intro i g
    simp only [Cover.rd, Pi.smul_apply, smul_eq_mul, adel_muPin]
    ring

end GlobalTheory.CoverIndep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisIntegralCoords
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section
namespace GlobalTheory.SingleDatum

theorem exists_basis_integral_coords : ∀ (F : IntermediateField ℚ ℂ) [NumberField F] (la : HeightOneSpectrum (𝓞 F)) (O : Subring ℂ), (∀ x : F, la.valuation F x ≤ 1 → (x : ℂ) ∈ O) → ∀ S : Set ℂ, S.Finite → S ⊆ O → ∃ (m : ℕ) (β : Fin m → ℂ) (lam : Fin m → (ℂ →ₗ[F] F)), (∀ k, β k ∈ O) ∧ ∀ x ∈ S, x = ∑ k, β k * (lam k x : ℂ) ∧ ∀ k, la.valuation F (lam k x) ≤ 1 := by
  intro F _ la O hO S hS hSO
  let R := (la.valuation F).integer
  have hsm : ∀ (r : R) (z : ℂ), r • z = (((r : F) : ℂ)) * z := fun r z => rfl
  let N : Submodule R ℂ := Submodule.span R S
  haveI : Module.Finite R N := Module.Finite.span_of_finite R hS
  haveI : Module.IsTorsionFree R N := inferInstance
  haveI : Module.Free R N := Module.free_of_finite_type_torsion_free'
  let b := (Module.Free.chooseBasis R N).reindex (Fintype.equivFin _)
  let m := Fintype.card (Module.Free.ChooseBasisIndex R N)
  let β : Fin m → ℂ := fun k => ((b k : N) : ℂ)
  have hliR : LinearIndependent R β := b.linearIndependent.map' N.subtype N.ker_subtype
  have hliF : LinearIndependent F β := (LinearIndependent.iff_fractionRing R F).1 hliR
  choose g hg using fun k : Fin m => LinearMap.exists_extend ((Finsupp.lapply k).comp hliF.repr)
  have key : ∀ k j, g k (β j) = if j = k then 1 else 0 := by
    intro k j
    have hmem : β j ∈ Submodule.span F (Set.range β) := Submodule.subset_span ⟨j, rfl⟩
    have := LinearMap.congr_fun (hg k) ⟨β j, hmem⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this, hliF.repr_eq_single j _ rfl]
    simp [Finsupp.single_apply]
  have hNO : ∀ z ∈ N, z ∈ O := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem y hy => exact hSO hy
    | zero => exact O.zero_mem
    | add y w _ _ hy hw => exact O.add_mem hy hw
    | smul r y _ hy =>
      rw [hsm]
      exact O.mul_mem (hO _ ((Valuation.mem_integer_iff _ _).1 r.2)) hy
  refine ⟨m, β, g, fun k => hNO _ (b k).2, ?_⟩
  intro x hx
  have hxN : x ∈ N := Submodule.subset_span hx
  let c : Fin m → F := fun j => ((b.repr ⟨x, hxN⟩ j : R) : F)
  have hxs : x = ∑ j, c j • β j := by
    have h := congrArg Subtype.val (b.sum_repr ⟨x, hxN⟩)
    rw [Submodule.coe_sum] at h
    refine h.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [Submodule.coe_smul, hsm, Algebra.smul_def]
    rfl
  have hg' : ∀ k, g k x = c k := by
    intro k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hxs, map_sum]
    simp only [map_smul, key, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine ⟨?_, fun k => ?_⟩
  · conv_lhs => rw [hxs]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hg', Algebra.smul_def, mul_comm]
    rfl
  · rw [hg']
    exact (Valuation.mem_integer_iff _ _).1 (b.repr ⟨x, hxN⟩ k).2

end GlobalTheory.SingleDatum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjLatUnimodBd
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ConjLatSplit

open GlobalTheory.UnRep GlobalTheory.UnRep.FullReps GlobalTheory.AdLat GlobalTheory.AdLat.Translate GlobalTheory.UnRep.SmallMat

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem exists_conjLat_unimod_bd (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (bad : ℕ)
    (h : GL (Fin n) (RA (maximalRealSubfield E) E)) (hh : IsUnA (IsCMField.complexConj E) 1 h.1)
    (hs : SuppSplit (IsCMField.complexConj E) bad h.1) :
    ∃ (Λ : Submodule (𝓞 E) (Fin n → E)) (k : ℕ),
      (Λ : Set (Fin n → E)) = latOf (maximalRealSubfield E) h.1 (Formalism.L2.Pj.stdLat E n) ∧ (conjLat H Λ).Unimod ∧
      k.Coprime bad ∧ ∀ u : ℕ, Ideal.span {((u * k : ℕ) : 𝓞 E)} • (conjLat H Λ).La ≤ Formalism.L2.Pj.stdLat E n ∧
        Ideal.span {((u * k : ℕ) : 𝓞 E)} • Formalism.L2.Pj.stdLat E n ≤ (conjLat H Λ).La := by
  obtain ⟨-, -, hfg, hsp, -⟩ := StdInhab.main E H n
  obtain ⟨Λ, hΛ, -⟩ := exists_lattice_latOf (maximalRealSubfield E) E n (Formalism.L2.Pj.stdLat E n) h hfg hsp
  obtain ⟨e, -, -, he, hcut⟩ := hs
  have hcut' := cut_inv h _ hcut
  have he' : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      ((bad : ℕ) : 𝓞 (maximalRealSubfield E)) ∈ v.asIdeal → e v = 0 := fun v hv => by
    by_contra h0
    exact (he v h0).2 hv
  obtain ⟨t, ht, hb⟩ := exists_nat_bd _ hfg hsp _ e he' _ hcut
  obtain ⟨t', ht', hb'⟩ := exists_nat_bd _ hfg hsp _ e he' _ hcut'
  refine ⟨Λ, t' * t, hΛ, conjLat_unimod H hh hΛ, Nat.Coprime.mul_left ht' ht, fun u => ?_⟩
  refine conjLat_le H (by rw [← H.bar_eq, map_natCast]) (smul_mem_of_bd hfg hsp hΛ ?_ ?_)
  · have := hb.mul ((u * t' : ℕ) : 𝓞 E)
    rwa [← Nat.cast_mul, mul_assoc] at this
  · have := hb'.mul ((u * t : ℕ) : 𝓞 E)
    rwa [← Nat.cast_mul, mul_assoc, mul_comm t] at this

end General

end GlobalTheory.ConjLatSplit


open GlobalTheory.ConjLatSplit in
theorem GlobalTheory.SingleDatum.exists_conjLat_levOK : ∀ (D : D7) (V : HSp D), V.gram = 1 → L0c D V = (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) → ∀ (bad M p : ℕ), Odd M → 2 ∣ bad → M ∣ bad → p ∣ bad → ∀ h : GA D V, SplitOffBad V bad h → ∃ (Λ : GenLat D.host.E V.rank) (u : ℕ), (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat V (finPt V h)) ∧ Λ.Unimod ∧ Λ.TrivAt M ∧ Nat.Coprime u p ∧ Λ.LevOK (M * u) M := by
  intro D V hg hL0 bad M p hM h2 hMb hpb h hs
  have hL : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank :=
    SetLike.coe_injective ((GlobalTheory.Equiv.StdSpace.identityClassLattice_eq_selfDualFrameLattice V).trans hL0)
  have hc : GlobalTheory.Member.cF D = IsCMField.complexConj D.host.E := AlgEquiv.ext fun _ => rfl
  have hu := GlobalTheory.UnRep.Space.isUnA_finHom V h
  rw [show (HSpace.gram V)ᵀ = 1 by rw [hg, Matrix.transpose_one], hc] at hu
  have hs' : GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) bad (finHom V h).1 :=
    (GlobalTheory.RepsCompare.suppSplitOff_iff _ _ _).1 (GlobalTheory.RepsCompare.suppSplitOff_of_splitOffBad _ _ _ hs)
  rw [hc] at hs'
  obtain ⟨Λ, k, h1, hU, hk, hnat⟩ := exists_conjLat_unimod_bd (Formalism.L2.Pj.hostOfRecord D) bad (finHom V h) hu hs'
  rw [GlobalTheory.SplitReps.hLat_one] at hL
  have e := GlobalTheory.SplitReps.hLat_eq V (FWT.fin V h) Λ (by rw [hL]; exact h1)
  have hk1 := hnat 1
  rw [one_mul] at hk1
  refine ⟨GlobalTheory.UnRep.FullReps.conjLat (Formalism.L2.Pj.hostOfRecord D) Λ, k, fun v => ?_, hU,
    ⟨k, hk.coprime_dvd_right hMb, hk1⟩, hk.coprime_dvd_right hpb,
    ⟨hM.mul (Nat.Coprime.odd_of_right (hk.coprime_dvd_right h2)), dvd_mul_right _ _,
      le_inf (hnat M).2 Submodule.smul_le_right⟩⟩
  change _ ↔ _ ∈ Bridge.hLat V (FWT.fin V h)
  rw [e]
  exact Iff.rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameTwistFamilySpecializationGoodStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameTwistFamily_specialization_good : ∀ (D : D7) (C A : Type) [AddCommGroup C] [CommGroup A] (u : UnivTwist D C) (Q : Finset (Pl D.host.E)) (χ : Multiplicative (↥Q → C) →* A), u.Good Q → (u.spec Q χ).Good := by
  first | exact @GlobalTheory.ExportSeries.SpecGood.spec_good | exact GlobalTheory.ExportSeries.SpecGood.spec_good | (intros; apply GlobalTheory.ExportSeries.SpecGood.spec_good <;> assumption)
end

