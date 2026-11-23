module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0384
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0368
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0388
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0399
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0427
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominanceOfWeylCharacterCoeff
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0413
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeTwistedIso
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibOrd.DerivTw

section gen

variable {G M V W : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem equiv_of_eq {ρ σ : Representation ℂ G V} (h : ρ = σ) : Nonempty (ρ.Equiv σ) :=
  h ▸ ⟨Representation.Equiv.refl _⟩

theorem twAct_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) (e : ρ.Equiv σ) :
    Nonempty ((twAct ρ N θ s hs).Equiv (twAct σ N θ s hs)) := by
  let f := twMap ρ σ N θ e.toLinearEquiv.toLinearMap (fun g v => eint e g v)
  let f' := twMap σ ρ N θ e.symm.toLinearEquiv.toLinearMap (fun g v => eint e.symm g v)
  refine ⟨Representation.Equiv.mk (LinearEquiv.ofLinear f f' ?_ ?_) fun x => ?_⟩
  · refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
    show Submodule.Quotient.mk (e (e.symm v)) = Submodule.Quotient.mk v
    simp
  · refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
    show Submodule.Quotient.mk (e.symm (e v)) = Submodule.Quotient.mk v
    simp
  · refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
    show Submodule.Quotient.mk (e (ρ (s x) v)) = Submodule.Quotient.mk (σ (s x) (e v))
    rw [eint e]

theorem twKer_twist (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) (χ : G →* ℂˣ) (hN : ∀ n : N, χ n = 1) :
    twKer (twist ρ χ) N θ = twKer ρ N θ := by
  unfold twKer
  congr 1
  ext w
  simp only [twist_apply, hN, Units.val_one, one_smul, Set.mem_setOf_eq]

theorem twAct_twist (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) (χ : G →* ℂˣ) (χ' : M →* ℂˣ)
    (hN : ∀ n : N, χ n = 1) (hχ : ∀ m, χ (s m) = χ' m) :
    Nonempty ((twAct (twist ρ χ) N θ s hs).Equiv (twist (twAct ρ N θ s hs) χ')) := by
  refine ⟨Representation.Equiv.mk (Submodule.quotEquivOfEq (twKer (twist ρ χ) N θ) (twKer ρ N θ) (twKer_twist ρ N θ χ hN)) fun x => ?_⟩
  refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
  show Submodule.Quotient.mk (p := twKer ρ N θ) ((χ (s x) : ℂ) • ρ (s x) v) =
    (χ' x : ℂ) • Submodule.Quotient.mk (p := twKer ρ N θ) (ρ (s x) v)
  rw [hχ]
  rfl

end gen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_of_last {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (h : A (Fin.last n) = eLast k n) :
    A.det = (blockMat k n A).det := by
  have h0 : ∀ j : Fin n, A (Fin.last n) (Fin.castSucc j) = 0 := fun j => by
    rw [h]; simp [eLast, Pi.single_apply, Fin.castSucc_ne_last]
  have h1 : A (Fin.last n) (Fin.last n) = 1 := by
    rw [h]; simp [eLast]
  rw [Matrix.det_succ_row A (Fin.last n), Fin.sum_univ_castSucc]
  simp only [h0, h1, Fin.succAbove_last]
  simp [blockMat, ← two_mul, Matrix.submatrix]
  rfl

theorem det_uin {n : ℕ} (u : MirUin k n) :
    Matrix.GeneralLinearGroup.det ((u : Mir k n) : GL (Fin (n + 1)) k) = 1 := by
  obtain ⟨v, hv⟩ := (u.2 : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  have hb : blockMat k n (((u : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = 1 := by
    rw [show ((u : Mir k n) : GL (Fin (n + 1)) k) = unip k n v from hv.symm]
    ext i j
    show (1 + colMat k n v.toAdd) (Fin.castSucc i) (Fin.castSucc j) = _
    simp [colMat, Matrix.one_apply, Fin.castSucc_ne_last]
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, det_of_last _ ((mem_Mir_iff k _).1 (u : Mir k n).2), hb]
  simp

theorem det_levi {n : ℕ} (m : GL (Fin n) k) :
    Matrix.GeneralLinearGroup.det ((levi k n m : Mir k n) : GL (Fin (n + 1)) k) = Matrix.GeneralLinearGroup.det m := by
  have hb : blockMat k n (((levi k n m : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      (m : Matrix (Fin n) (Fin n) k) := by
    ext i j
    show glEmbMat k n (m : Matrix (Fin n) (Fin n) k) (Fin.castSucc i) (Fin.castSucc j) = _
    simp [glEmbMat]
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    det_of_last _ ((mem_Mir_iff k _).1 (levi k n m : Mir k n).2), hb]

theorem dpow_add (n : ℕ) (s t : ℝ) : dpow (k := k) n (s + t) = dpow n t * dpow n s := by
  ext g
  simp only [dpow, detChar_apply, MonoidHom.mul_apply, Complex.ofReal_add, absPow_add, Units.val_mul]
  exact mul_comm _ _

theorem dpow_zero (n : ℕ) : dpow (k := k) n 0 = 1 := by
  ext g
  simp [dpow]

theorem dpowM_add (n : ℕ) (s t : ℝ) : dpowM (k := k) n (s + t) = dpowM n t * dpowM n s := by
  ext g
  simp [dpowM, dpow_add]

theorem dpowM_zero (n : ℕ) : dpowM (k := k) n 0 = 1 := by
  ext g
  simp [dpowM, dpow_zero]

theorem dpowM_uin {n : ℕ} (s : ℝ) (u : MirUin k n) : dpowM n s (u : Mir k n) = 1 := by
  show detChar (Fin (n + 1)) (absPow k (s : ℂ)) ((u : Mir k n) : GL (Fin (n + 1)) k) = 1
  rw [detChar_apply, det_uin, map_one]

theorem dpowM_levi {n : ℕ} (s : ℝ) (m : GL (Fin n) k) : dpowM n s (levi k n m) = dpow n s m := by
  show detChar (Fin (n + 1)) (absPow k (s : ℂ)) ((levi k n m : Mir k n) : GL (Fin (n + 1)) k) = _
  rw [detChar_apply, det_levi]
  rfl

theorem tw_tw {n : ℕ} (π : GRep k n) (s t : ℝ) : GIso ((π.tw s).tw t) (π.tw (s + t)) := by
  show Nonempty ((twist (twist π.ρ (dpow n s)) (dpow n t)).Equiv (twist π.ρ (dpow n (s + t))))
  exact equiv_of_eq (by rw [twist_twist, dpow_add])

theorem tw_zero {n : ℕ} (π : GRep k n) : GIso (π.tw 0) π := by
  show Nonempty ((twist π.ρ (dpow n 0)).Equiv π.ρ)
  exact equiv_of_eq (by rw [dpow_zero, twist_one])

theorem mtw_mtw {n : ℕ} (τ : MRep k n) (s t : ℝ) : MIso (mtw (mtw τ s) t) (mtw τ (s + t)) := by
  show Nonempty ((twist (twist τ.ρ (dpowM n s)) (dpowM n t)).Equiv (twist τ.ρ (dpowM n (s + t))))
  exact equiv_of_eq (by rw [twist_twist, dpowM_add])

theorem mtw_zero {n : ℕ} (τ : MRep k n) : MIso (mtw τ 0) τ := by
  show Nonempty ((twist τ.ρ (dpowM n 0)).Equiv τ.ρ)
  exact equiv_of_eq (by rw [dpowM_zero, twist_one])

theorem miso_mtw {n : ℕ} {A B : MRep k n} (s : ℝ) (h : MIso A B) : MIso (mtw A s) (mtw B s) := by
  obtain ⟨e⟩ := h
  exact ⟨Representation.Equiv.mk e.toLinearEquiv fun x => by
    ext v
    show e (((dpowM n s x : ℂˣ) : ℂ) • A.ρ x v) = ((dpowM n s x : ℂˣ) : ℂ) • B.ρ x (e v)
    rw [map_smul]
    exact congrArg _ (eint e x v)⟩

def psiG {n : ℕ} (τ : MRep k n) : GRep k n := ⟨_, psiMinus k τ.ρ⟩

theorem miso_phiM (ψ : AddChar k Circle) {n : ℕ} {A B : MRep k (n + 1)} (h : MIso A B) :
    MIso (MRep.phiM k ψ A) (MRep.phiM k ψ B) := by
  obtain ⟨e⟩ := h
  exact twAct_equiv _ _ _ (levi_stab ψ n) e

theorem giso_psiG {n : ℕ} {A B : MRep k n} (h : MIso A B) : GIso (psiG A) (psiG B) := by
  obtain ⟨e⟩ := h
  exact twAct_equiv _ _ _ (levi_normalises n) e

theorem phiM_mtw (ψ : AddChar k Circle) {n : ℕ} (τ : MRep k (n + 1)) (s : ℝ) :
    MIso (MRep.phiM k ψ (mtw τ s)) (mtw (MRep.phiM k ψ τ) s) :=
  twAct_twist τ.ρ _ _ _ (levi_stab ψ n) (dpowM (n + 1) s) (dpowM n s) (dpowM_uin s) fun m => by
    show dpowM (n + 1) s (levi k (n + 1) (m : GL (Fin (n + 1)) k)) = _
    rw [dpowM_levi]
    rfl

theorem psiG_mtw {n : ℕ} (τ : MRep k n) (s : ℝ) : GIso (psiG (mtw τ s)) ((psiG τ).tw s) :=
  twAct_twist τ.ρ _ _ _ (levi_normalises n) (dpowM n s) (dpow n s) (dpowM_uin s) (dpowM_levi s)

theorem miso_iterPhi (ψ : AddChar k Circle) {n : ℕ} : ∀ (j : ℕ) {A B : MRep k (n + j)}, MIso A B →
    MIso (iterPhi k ψ j A) (iterPhi k ψ j B)
  | 0, _, _, h => h
  | j + 1, _, _, h => miso_iterPhi ψ j (miso_phiM ψ h)

theorem iterPhi_mtw (ψ : AddChar k Circle) {n : ℕ} (s : ℝ) : ∀ (j : ℕ) (X : MRep k (n + j)),
    MIso (iterPhi k ψ j (mtw X s)) (mtw (iterPhi k ψ j X) s)
  | 0, _ => miso_refl _
  | j + 1, X => miso_trans (miso_iterPhi ψ j (phiM_mtw ψ X s)) (iterPhi_mtw ψ s j (MRep.phiM k ψ X))

theorem iterN_iso (ψ : AddChar k Circle) {n : ℕ} : ∀ (j : ℕ) (τ : MRep k (n + j)),
    MIso (iterN ψ j τ) (mtw (iterPhi k ψ j τ) (-(j : ℝ) / 2))
  | 0, τ => by
    rw [show -((0 : ℕ) : ℝ) / 2 = 0 by simp]
    exact miso_symm (mtw_zero τ)
  | j + 1, τ => by
    have h1 := iterN_iso ψ j (phiN ψ τ)
    have h2 := iterPhi_mtw ψ (-1 / 2) j (MRep.phiM k ψ τ)
    have h3 := mtw_mtw (iterPhi k ψ j (MRep.phiM k ψ τ)) (-1 / 2) (-(j : ℝ) / 2)
    rw [show (-1 / 2 : ℝ) + -(j : ℝ) / 2 = -((j + 1 : ℕ) : ℝ) / 2 by push_cast; ring] at h3
    exact miso_trans h1 (miso_trans (miso_mtw _ h2) h3)

theorem derivB_iso_tw : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (j n : ℕ) (π : GRep k (n + j)), GIso (derivB ψ j π) ((dG ψ j π).tw ((j : ℝ) / 2)) := by
  intro k _ _ _ _ ψ j n π
  cases j with
  | zero =>
    rw [show ((0 : ℕ) : ℝ) / 2 = 0 by simp]
    exact giso_symm (tw_zero π)
  | succ j =>
    have h1 : MIso (iterN ψ j (gres π)) (mtw (iterPhi k ψ j (resM k π.ρ)) (-(j : ℝ) / 2)) := iterN_iso ψ j (gres π)
    have h2 : GIso (psiN (iterN ψ j (gres π))) ((psiG (mtw (iterPhi k ψ j (resM k π.ρ)) (-(j : ℝ) / 2))).tw (-1 / 2)) :=
      giso_tw _ (giso_psiG h1)
    have h3 := giso_tw (-1 / 2) (psiG_mtw (iterPhi k ψ j (resM k π.ρ)) (-(j : ℝ) / 2))
    have h4 := tw_tw (psiG (iterPhi k ψ j (resM k π.ρ))) (-(j : ℝ) / 2) (-1 / 2)
    have h5 : GIso ((dG ψ (j + 1) π).tw (((j + 1 : ℕ) : ℝ) / 2))
        (((psiG (iterPhi k ψ j (resM k π.ρ))).tw (-(j : ℝ) / 2 + -1 / 2)).tw (((j + 1 : ℕ) : ℝ) / 2)) :=
      giso_tw _ (giso_trans h2 (giso_trans h3 h4))
    have h6 := tw_tw (psiG (iterPhi k ψ j (resM k π.ρ))) (-(j : ℝ) / 2 + -1 / 2) (((j + 1 : ℕ) : ℝ) / 2)
    rw [show -(j : ℝ) / 2 + -1 / 2 + ((j + 1 : ℕ) : ℝ) / 2 = 0 by push_cast; ring] at h6
    exact giso_symm (giso_trans h5 (giso_trans h6 (tw_zero _)))

end GlobalTheory.CompanionTheory.LeibOrd.DerivTw

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualWeightsDominated
section
noncomputable section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG GlobalTheory.CompanionTheory.RealCount.Tope

namespace GlobalTheory.CompanionTheory.RealCountG.TopeG

theorem cPoly_coeff {n : ℕ} (s : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ) (μ : Fin n → ℤ) :
    (cPoly s c).coeff μ = if μ ∈ s then c μ else 0 := by
  classical
  unfold cPoly
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [Finset.sum_ite_eq']

theorem trOn_dualT_id {n : ℕ} (E : KMod n) (S : Submodule ℂ (E.V →L[ℂ] ℂ)) :
    trOn S (dualT E 1 : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) = Module.finrank ℂ S := by
  have h1 : (dualT E 1 : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) = LinearMap.id := by
    ext ξ v
    simp [dualT]
  rw [h1]
  unfold trOn
  rw [dite_eq_left (fun x hx => by simpa using hx)]
  have h2 : (LinearMap.id : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)).restrict (fun x (hx : x ∈ S) => hx) = LinearMap.id := by
    ext x; rfl
  rw [h2, LinearMap.trace_id]

theorem topeG : ∀ {n : ℕ} (lam : Fin n → ℤ), Antitone lam → ∀ (E : KMod n) (T : E.V →L[ℂ] E.V), IsLefK lam E T →
    (⨆ μ, wtDual E μ) = ⊤ ∧ ∀ μ, wtDual E μ ≠ ⊥ → DomLE (wtR μ) (m0 lam) := by
  intro n lam hlam E T hT
  have hspan := _root_.GlobalTheory.CompanionTheory.RealCount.Tope.iSup_wtDual_eq_top E
  have hind := GlobalTheory.CompanionTheory.RealCount.Tope.wtDual_iSupIndep E
  have hfin : Set.Finite {μ | wtDual E μ ≠ ⊥} := WellFoundedGT.finite_ne_bot_of_iSupIndep hind
  set s := hfin.toFinset with hs
  have hmem : ∀ μ, wtDual E μ ≠ ⊥ → μ ∈ s := fun μ h => by simpa [hs] using h
  obtain ⟨h1, -⟩ := GlobalTheory.T.weight_polynomial_trace_identity lam E T hT hspan hind s hmem
  refine ⟨hspan, fun μ hμ => _root_.GlobalTheory.CompanionTheory.RealCountG.DomA.domLE_of_mul_eq lam hlam _ h1 μ ?_⟩
  rw [cPoly_coeff, if_pos (hmem μ hμ), trOn_dualT_id]
  have : Module.finrank ℂ (wtDual E μ) ≠ 0 := fun h0 => hμ (Submodule.finrank_eq_zero.1 h0)
  exact_mod_cast this

end GlobalTheory.CompanionTheory.RealCountG.TopeG
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHeckeFunctional
section
noncomputable section

namespace GlobalTheory.CompanionTheory.EisRat

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter _root_.Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem hgt_par_mul {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} (hK : IsHgt K a) {p : G2 σ Y} {t : GL (Fin n) (AE F E)}
    (hp : IsPar p t) (x : G2 σ Y) :
    a (p * x) = (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) * a x := by
  obtain ⟨p', t', hp', k, hk, rfl⟩ := hK.iwa x
  rw [← mul_assoc, hK.val _ _ (hp.mul hp') k hk, hK.val _ _ hp' k hk, map_mul, map_mul]
  push_cast
  rfl

theorem hgt_nonneg {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} (hK : IsHgt K a) (x : G2 σ Y) : 0 ≤ a x := by
  obtain ⟨p, t, hp, k, hk, rfl⟩ := hK.iwa x
  rw [hK.val _ _ hp k hk]
  exact NNReal.coe_nonneg _

theorem absE_ne_zero (u : (AF F ⊗[F] E)ˣ) : ((absE F E u : ℝ) : ℂ) ≠ 0 := by
  have h : absE F E u ≠ 0 := ((absE F E).toHomUnits u).ne_zero
  exact_mod_cast h

theorem law_flat {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} (hK : IsHgt K a) {χ : Chr F E} {s₁ : ℂ} {f : G2 σ Y → ℂ}
    (hf : IsSec K χ s₁ f) (s : ℂ) : Law χ (s + n / 2) (flat a f s₁ s) := by
  intro p t x hp
  have hd := absE_ne_zero (F := F) (E := E) (Matrix.GeneralLinearGroup.det t)
  have h0 : (0 : ℝ) ≤ (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) := NNReal.coe_nonneg _
  have hc : ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ (s + (n : ℂ) / 2) =
      ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ (s - s₁) *
        ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ (s₁ + (n : ℂ) / 2) := by
    rw [← Complex.cpow_add _ _ hd]
    congr 1
    ring
  simp only [flat]
  rw [hgt_par_mul hK hp x, hf.law p t x hp, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg h0 (hgt_nonneg hK x), hc]
  ring

end GlobalTheory.CompanionTheory.EisRat

namespace GlobalTheory.CompanionTheory.EisRat

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter _root_.Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

theorem eis_left_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → IsHecke F E χ → ∀ (t : ℝ) (Ê : ℂ → G2 σ Y → ℂ), (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) → ∀ s : ℂ, t < s.re → ∀ γ ∈ rat2 σ Y, ∀ x, Ê s (γ * x) = Ê s x := by
  intro F E _ _ _ _ _ σ B n Y r s _ _ _ b K a _ _ hK χ s₁ f hf hχ t Ê hs s' hs' γ hγ x
  exact (law_flat hK hf s').eis_rat hχ (hs s' hs') hγ x

end GlobalTheory.CompanionTheory.EisRat

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbBar
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.CompanionTheory.GodementH

section Defs

variable (F : Type) [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]

def embBar (v : Pl (F := F)) : E →ₐ[F] FvBar F v := IsAlgClosed.lift

variable {F E} {J : Type} [Fintype J]

def supBar (v : Pl (F := F)) (τ : E →ₐ[F] FvBar F v) (u : J → E) : ℝ≥0 :=
  Finset.univ.sup fun f => absBar F v (τ (u f))

def locFin (σ : E →ₐ[F] E) (v : Pl (F := F)) (u : J → E) : ℝ≥0 :=
  supBar v (embBar F E v) u * supBar v ((embBar F E v).comp σ) u


open Classical in
def locInf (w : InfinitePlace F) (u : J → E) : ℝ≥0 :=
  (Finset.univ.sup fun p : EmbOver E w × J => ‖p.1.1 (u p.2)‖₊) ^ 2

def vecHt (σ : E →ₐ[F] E) (u : J → E) : ℝ≥0 := (∏ w : InfinitePlace F, locInf w u) * ∏ᶠ v, locFin σ v u

end Defs

section Minors

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

def mnr (M : Matrix ι (Fin n) R) (f : Fin n → ι) : R := (M.submatrix f id).det

end Minors

end GlobalTheory.CompanionTheory.GodementH

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactConjugacyTransversal
section
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

namespace GlobalTheory.CompanionTheory.OrbitalCount

theorem exists_compact_reps_of_finite_doubleCosets :
    ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (K : Subgroup H) (N : H),
      IsCompact (K : Set H) →
      (∀ C : Set H, IsCompact C →
        {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) N : Set H) (K : Set H) |
          ∃ k ∈ K, (Quotient.out q * k)⁻¹ * N * MonoidHom.id H (Quotient.out q * k) ∈ C}.Finite) →
      ∀ C : Set H, IsCompact C →
        ∃ D : Set H, IsCompact D ∧ ∀ x : H, x⁻¹ * N * x ∈ C →
          ∃ t ∈ twCent (MonoidHom.id H) N, ∃ d ∈ D, x = t * d := by
  intro H _ _ _ K N hK hfin C hC
  refine ⟨⋃ q ∈ {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) N : Set H) (K : Set H) |
      ∃ k ∈ K, (Quotient.out q * k)⁻¹ * N * MonoidHom.id H (Quotient.out q * k) ∈ C},
      (fun k => Quotient.out q * k) '' (K : Set H), ?_, ?_⟩
  · exact (hfin C hC).isCompact_biUnion fun q _ =>
      hK.image (continuous_const.mul continuous_id)
  · intro x hx
    obtain ⟨h, hh, k, hk, hout⟩ :=
      DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id H) N) K x
    have hcomm : h * N = N * h := hh
    have hconj : (h * x)⁻¹ * N * (h * x) = x⁻¹ * N * x := by
      have : h⁻¹ * N * h = N := by
        rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
      calc (h * x)⁻¹ * N * (h * x) = x⁻¹ * (h⁻¹ * N * h) * x := by group
        _ = x⁻¹ * N * x := by rw [this]
    set q := DoubleCoset.mk (twCent (MonoidHom.id H) N) K x with hq
    have hd : Quotient.out q * k⁻¹ = h * x := by
      rw [hout]; group
    refine ⟨h⁻¹, inv_mem hh, Quotient.out q * k⁻¹, ?_, ?_⟩
    · refine Set.mem_biUnion (x := q) ?_ ⟨k⁻¹, inv_mem hk, rfl⟩
      refine ⟨k⁻¹, inv_mem hk, ?_⟩
      rw [MonoidHom.id_apply, hd, hconj]
      exact hx
    · rw [hd, inv_mul_cancel_left]

end GlobalTheory.CompanionTheory.OrbitalCount
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmallCompactOpenBetween
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

theorem exists_compactOpen_between_mul_small
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hbase : ∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (K₀ C : Subgroup G) (hK₀o : IsOpen (K₀ : Set G)) (hK₀c : IsCompact (K₀ : Set G)) (hC : C ≤ K₀)
    (N : Set G) (hN : N ∈ 𝓝 (1 : G)) :
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ C ≤ K ∧ K ≤ K₀ ∧
      ∀ x ∈ K, ∃ n ∈ N, ∃ c ∈ C, x = n * c := by
  obtain ⟨K₆, hK₆o, -, hK₆s⟩ := hbase ((K₀ : Set G) ∩ N)
    (Filter.inter_mem (hK₀o.mem_nhds K₀.one_mem) hN)
  haveI : CompactSpace K₀ := isCompact_iff_compactSpace.mp hK₀c

  set H : Subgroup K₀ := K₆.subgroupOf K₀ with hH
  have hHo : IsOpen (H : Set K₀) := hK₆o.preimage continuous_subtype_val
  haveI : Finite (K₀ ⧸ H) := H.quotient_finite_of_isOpen hHo
  haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  set M : Subgroup K₀ := H.normalCore with hM
  have hMH : M ≤ H := Subgroup.normalCore_le H
  have hHc : IsClosed (H : Set K₀) := OpenSubgroup.isClosed ⟨H, hHo⟩
  have hMc : IsClosed (M : Set K₀) := by
    have : (M : Set K₀) = ⋂ b : K₀, (fun a : K₀ => b * a * b⁻¹) ⁻¹' (H : Set K₀) := by
      ext a
      simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
      exact Iff.rfl
    rw [this]
    exact isClosed_iInter fun b => hHc.preimage (by fun_prop)
  haveI : M.FiniteIndex := Subgroup.finiteIndex_normalCore H
  have hMo : IsOpen (M : Set K₀) := Subgroup.isOpen_of_isClosed_of_finiteIndex M hMc

  set D : Subgroup K₀ := C.subgroupOf K₀ with hD
  set L : Subgroup K₀ := M ⊔ D with hL
  have hLo : IsOpen (L : Set K₀) := Subgroup.isOpen_mono (le_sup_left : M ≤ L) hMo
  have hLc : IsClosed (L : Set K₀) := OpenSubgroup.isClosed ⟨L, hLo⟩
  have himg : ((L.map K₀.subtype : Subgroup G) : Set G) = Subtype.val '' (L : Set K₀) := by
    ext x; simp [Subgroup.mem_map]
  refine ⟨L.map K₀.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rw [himg]
    exact hK₀o.isOpenMap_subtype_val _ hLo
  · rw [himg]
    exact hLc.isCompact.image continuous_subtype_val
  · intro c hc
    refine ⟨⟨c, hC hc⟩, ?_, rfl⟩
    exact (le_sup_right : D ≤ L) (by simpa [hD, Subgroup.mem_subgroupOf] using hc)
  · exact Subgroup.map_subtype_le L
  · rintro x ⟨y, hy, rfl⟩
    have hy' : y ∈ ((M ⊔ D : Subgroup K₀) : Set K₀) := hy
    rw [Subgroup.normal_mul] at hy'
    obtain ⟨m, hm, d, hd, rfl⟩ := Set.mem_mul.mp hy'
    refine ⟨(m : G), (hK₆s (hMH hm)).2, (d : G), hd, rfl⟩

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end

