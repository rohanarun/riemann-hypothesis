module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLevi
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyExhaustion.PropsExh
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0720
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0355
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLength
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0532
public import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0544
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetQuotientEigenvector
section
noncomputable section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.JacExp

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem exists_atom_le {ρ : Representation ℂ G V} (h : HasFiniteLength ρ) {E : Subrepresentation ρ}
    (hE : E ≠ ⊥) : ∃ S : Subrepresentation ρ, IsAtom S ∧ S ≤ E := by
  obtain ⟨-, hw⟩ := (hasFiniteLength_iff_wellFounded ρ).1 h
  haveI : IsAtomic (Subrepresentation ρ) := isAtomic_of_orderBot_wellFounded_lt hw
  obtain h' | ⟨S, hS, hle⟩ := eq_bot_or_exists_atom_le E
  · exact absurd h' hE
  · exact ⟨S, hS, hle⟩

def eigenSub (ρ : Representation ℂ G V) (z : G) (hz : ∀ g, z * g = g * z) (ν : ℂ) : Subrepresentation ρ :=
  ⟨Module.End.eigenspace (ρ z) ν, fun g v hv => by
    have hv' : ρ z v = ν • v := Module.End.mem_eigenspace_iff.1 hv
    refine Module.End.mem_eigenspace_iff.2 ?_
    have : ρ z (ρ g v) = ρ g (ρ z v) := by
      rw [← Module.End.mul_apply, ← map_mul, hz, map_mul, Module.End.mul_apply]
    rw [this, hv', map_smul]⟩

theorem mem_eigenSub {ρ : Representation ℂ G V} {z : G} {hz : ∀ g, z * g = g * z} {ν : ℂ} {v : V} :
    v ∈ (eigenSub ρ z hz ν).toSubmodule ↔ ρ z v = ν • v :=
  Module.End.mem_eigenspace_iff

theorem isSmooth_sub [TopologicalSpace G] {ρ : Representation ℂ G V} (h : IsSmooth ρ)
    (S : Subrepresentation ρ) : IsSmooth S.toRepresentation := fun v => by
  have : {g : G | S.toRepresentation g v = v} = {g : G | ρ g v.1 = v.1} := by
    ext g
    exact Subtype.ext_iff
  rw [this]
  exact h v.1

end General

section Tensor

variable {Γ X Y : Fin 2 → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
  [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]

theorem piTensor_apply_of_scalar (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (g : ∀ a, Γ a) (c : ℂ)
    (h0 : ∀ v, ρ 0 (g 0) v = c • v) (h1 : ∀ v, ρ 1 (g 1) v = v) (z : PiTensorProduct ℂ X) :
    piTensor ρ g z = c • z := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, piTensor_tprod, smul_comm]
    congr 1
    have : (fun a => ρ a (g a) (f a)) = Function.update f 0 (c • f 0) := by
      funext a
      fin_cases a
      · simp [h0]
      · simp [h1]
    rw [this, MultilinearMap.map_update_smul, Function.update_eq_self]
    rfl
  | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]

def piTensorCongr {ρ : ∀ a, Representation ℂ (Γ a) (X a)} {σ : ∀ a, Representation ℂ (Γ a) (Y a)}
    (φ : ∀ a, (ρ a).Equiv (σ a)) : (piTensor ρ).Equiv (piTensor σ) :=
  .mk (PiTensorProduct.congr fun a => (φ a).toLinearEquiv) fun g => by
    apply PiTensorProduct.ext
    ext f
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      piTensor_tprod, PiTensorProduct.congr_tprod]
    exact congrArg _ (funext fun a => (φ a).toIntertwiningMap.isIntertwining _ _ (g a) (f a))

end Tensor

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def omegaLevi (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : Fin 2 → ℕ) : Levi k (fun a => Fin (d a)) :=
  fun a => Matrix.GeneralLinearGroup.scalar (Fin (d a)) (if a = 0 then Zls.unifU k else 1)

theorem omegaLevi_comm (d : Fin 2 → ℕ) (h : Levi k (fun a => Fin (d a))) :
    omegaLevi k d * h = h * omegaLevi k d := by
  funext a
  apply Units.ext
  simp only [omegaLevi, Matrix.GeneralLinearGroup.scalar, Pi.mul_apply, Units.val_mul, Units.coe_map,
    MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  exact Matrix.scalar_commute _ (fun r => Commute.all _ _) _

theorem diagPow_val (N : ℕ) (lam : Fin N → ℤ) :
    (Zls.diagPow k N lam : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal fun i => ((Zls.unifU k ^ lam i : kˣ) : k) := rfl

theorem leviEmb_omegaLevi {N : ℕ} (d : Fin 2 → ℕ) (hd : ∑ a, d a = N) :
    leviEmb k (stdBlocks d hd) (omegaLevi k d) = Zls.diagPow k N (Zls.omegaVec N (d 0)) := by
  apply Units.ext
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks d hd).surjective j
  rw [diagPow_val]
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    by_cases hij : i = j
    · subst hij
      have hv := stdBlocks_val d hd a i
      have : (((stdBlocks d hd ⟨a, i⟩ : Fin N) : ℕ) < d 0) ↔ a = 0 := by
        rw [hv]
        fin_cases a
        · simp
        · simp
      simp [omegaLevi, Zls.omegaVec, this, Matrix.GeneralLinearGroup.scalar]
    · have : (stdBlocks d hd ⟨a, i⟩) ≠ (stdBlocks d hd ⟨a, j⟩) := by simpa using hij
      simp [omegaLevi, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply_ne _ this, hij]
  · have : (stdBlocks d hd ⟨a, i⟩) ≠ (stdBlocks d hd ⟨b, j⟩) := fun h =>
      hab (congrArg Sigma.fst ((stdBlocks d hd).injective h))
    rw [leviEmb_apply_ne k _ _ hab, Matrix.diagonal_apply_ne _ this]

theorem deltaHalf_omegaLevi (d : Fin 2 → ℕ) :
    (((deltaHalf k (fun a => Fin (d a)) (omegaLevi k d))⁻¹ : ℂˣ) : ℂ) =
      (Nat.card 𝓀[k] : ℂ) ^ (((d 0 * d 1 : ℕ) : ℂ) / 2) := by
  have h0 : modExp (fun a : Fin 2 => Fin (d a)) 0 = d 1 := by
    simp [modExp, Finset.sum_filter, Fin.sum_univ_two]
  have hd0 : Matrix.GeneralLinearGroup.det (omegaLevi k d 0) = Zls.unifU k ^ d 0 := by
    apply Units.ext
    simp [omegaLevi, Matrix.GeneralLinearGroup.scalar]
  have hd1 : Matrix.GeneralLinearGroup.det (omegaLevi k d 1) = 1 := by
    apply Units.ext
    simp [omegaLevi, Matrix.GeneralLinearGroup.scalar]
  have hn : nabs k (Zls.unifU k) = (resCard k : ℝ)⁻¹ :=
    nabs_uniformiser Zls.irreducible_unif rfl
  rw [deltaHalf_apply, Fin.prod_univ_two, hd0, hd1, map_one, mul_one, map_pow, h0]
  have hq : ((((resCard k : ℝ)⁻¹ : ℝ)) : ℂ) = ((Nat.card 𝓀[k] : ℂ))⁻¹ := by simp [resCard]
  have harg : Complex.arg (Nat.card 𝓀[k] : ℂ) ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact Real.pi_pos.ne
  rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, val_absPow, hn, hq, Complex.inv_cpow _ _ harg,
    inv_pow, inv_inv, ← Complex.cpow_nat_mul]
  congr 1
  push_cast
  ring

theorem exists_scalarBy (x : IrrGL (k := k)) (t : kˣ) : ∃ c : ℂ, Zl.ScalarBy x t c := by
  obtain ⟨ω, -, hω⟩ := ((schur_and_segments k).1 (Fin x.1) _ x.rep x.2.rep.smooth x.2.rep.irr).2
  exact ⟨ω t, fun v => hω t v⟩

theorem jm_ne_zero_of_equiv {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hx : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (S : Subrepresentation (GlobalTheory.SmGL.jac (stdBlocks (fun a => (x a).1) hx) π))
    (Φ : S.toRepresentation.Equiv (piTensor fun a => (x a).rep)) : Zc.jm x hx π ≠ 0 :=
  jhMult_ne_zero_iff.2 ⟨S, Φ.toIntertwiningMap, Φ.surjective⟩

theorem exists_constituent (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible) (d : Fin 2 → ℕ)
    (hd : ∑ a, d a = N) (μ : ℂ) (w : V)
    (hw : (Submodule.Quotient.mk w : Jacquet π (unipRad k (stdBlocks d hd))) ≠ 0)
    (hμ : (Submodule.Quotient.mk (π (Zls.diagPow k N (Zls.omegaVec N (d 0))) w) :
        Jacquet π (unipRad k (stdBlocks d hd))) =
      μ • (Submodule.Quotient.mk w : Jacquet π (unipRad k (stdBlocks d hd)))) :
    ∃ (x : Fin 2 → IrrGL (k := k)) (hx : ∑ a, (x a).1 = N), (∀ a, (x a).1 = d a) ∧ Zc.jm x hx π ≠ 0 ∧
      Zl.ScalarBy (x 0) (Zls.unifU k) (μ * (Nat.card 𝓀[k] : ℂ) ^ (((d 0 * d 1 : ℕ) : ℂ) / 2)) ∧
      ∃ c1 : ℂ, Zl.ScalarBy (x 1) (Zls.unifU k) c1 := by
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have hfl : HasFiniteLength (GlobalTheory.SmGL.jac (stdBlocks d hd) π) :=
    (hBZ k).2.1 (Fin 2) (Fin N) (fun a => Fin (d a)) (stdBlocks d hd) V π hs
      (hasFiniteLength_of_isIrreducible hi)
  set ν : ℂ := μ * (Nat.card 𝓀[k] : ℂ) ^ (((d 0 * d 1 : ℕ) : ℂ) / 2) with hν
  set w' : Jacquet π (unipRad k (stdBlocks d hd)) := Submodule.Quotient.mk w with hw'
  have heig : GlobalTheory.SmGL.jac (stdBlocks d hd) π (omegaLevi k d) w' = ν • w' := by
    rw [hw', jac_mk, leviEmb_omegaLevi, hμ, deltaHalf_omegaLevi, smul_smul, hν, mul_comm]
  set E := eigenSub (GlobalTheory.SmGL.jac (stdBlocks d hd) π) (omegaLevi k d) (omegaLevi_comm d) ν with hE
  have hEne : E ≠ ⊥ := by
    intro h
    have : w' ∈ E.toSubmodule := mem_eigenSub.2 heig
    rw [h] at this
    exact hw ((Submodule.mem_bot ℂ).1 this)
  obtain ⟨S, hS, hSE⟩ := exists_atom_le hfl hEne
  have hSirr : S.toRepresentation.IsIrreducible := GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom S hS
  let τ : IrrRep (Levi k fun a => Fin (d a)) :=
    ⟨S.toSubmodule, S.toRepresentation, isSmooth_sub (isSmooth_jac _ hs) S, hSirr⟩
  obtain ⟨s, ⟨Φ⟩⟩ := GlobalTheory.LeviFactor.exists_equiv_piTensor_levi hBZ k (Fin 2) (fun a => Fin (d a)) τ
  let x : Fin 2 → IrrGL (k := k) := fun a => IrrGL.of (N := d a) (s a).ρ (s a).smooth (s a).irr
  let Ψ : S.toRepresentation.Equiv (piTensor fun a => (x a).rep) :=
    Φ.trans (piTensorCongr fun a => IrrGL.equivOf (N := d a) (s a).ρ (s a).smooth (s a).irr)
  obtain ⟨c₀, hc₀⟩ := exists_scalarBy (x 0) (Zls.unifU k)
  obtain ⟨c₁, hc₁⟩ := exists_scalarBy (x 1) (Zls.unifU k)
  refine ⟨x, hd, fun a => rfl, jm_ne_zero_of_equiv x hd π S Ψ, ?_, c₁, hc₁⟩
  have hSne : S.toSubmodule ≠ ⊥ := fun h => hS.1 (Subrepresentation.ext h)
  obtain ⟨v₀, hv₀, hv₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSne
  let v : S.toSubmodule := ⟨v₀, hv₀⟩
  have hv : v ≠ 0 := fun h => hv₀ne (congrArg Subtype.val h)
  have h1 : S.toRepresentation (omegaLevi k d) v = ν • v := Subtype.ext (mem_eigenSub.1 (hSE hv₀))
  have h2 : piTensor (fun a => (x a).rep) (omegaLevi k d) (Ψ v) = c₀ • Ψ v := by
    refine piTensor_apply_of_scalar _ _ c₀ (fun u => ?_) (fun u => ?_) _
    · have : omegaLevi k d 0 = Matrix.GeneralLinearGroup.scalar (Fin (x 0).1) (Zls.unifU k) := by
        simp [omegaLevi]
        rfl
      rw [this]
      exact hc₀ u
    · have : omegaLevi k d 1 = 1 := by simp [omegaLevi]
      rw [this]
      exact LinearMap.congr_fun (map_one (x 1).rep) u
  have h3 : Ψ (S.toRepresentation (omegaLevi k d) v) =
      piTensor (fun a => (x a).rep) (omegaLevi k d) (Ψ v) :=
    Ψ.toIntertwiningMap.isIntertwining _ _ _ v
  have h4 : Ψ v ≠ 0 := fun h => hv (Ψ.toLinearEquiv.injective (by simpa using h))
  have h5 : ν • Ψ v = c₀ • Ψ v := by
    rw [← h2, ← h3, h1, map_smul]
  have h6 : c₀ = ν := (smul_left_injective ℂ h4 h5).symm
  rw [← h6]
  exact hc₀

theorem exists_constituent_of_eigen : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.Published.StandardFunctorsFiniteLength → ∀ (d : Fin 2 → ℕ) (hd : ∑ a, d a = N), 0 < d 0 → 0 < d 1 → ∀ (μ : ℂ) (w : V), (Submodule.Quotient.mk w : Jacquet π (unipRad k (stdBlocks d hd))) ≠ 0 → (Submodule.Quotient.mk (π (Zls.diagPow k N (Zls.omegaVec N (d 0))) w) : Jacquet π (unipRad k (stdBlocks d hd))) = μ • (Submodule.Quotient.mk w : Jacquet π (unipRad k (stdBlocks d hd))) → ∃ (x : Fin 2 → IrrGL (k := k)) (hx : ∑ a, (x a).1 = N), (∀ a, (x a).1 = d a) ∧ Zc.jm x hx π ≠ 0 ∧ Zl.ScalarBy (x 0) (Zls.unifU k) (μ * (Nat.card 𝓀[k] : ℂ) ^ (((d 0 * d 1 : ℕ) : ℂ) / 2)) ∧ ∃ c1 : ℂ, Zl.ScalarBy (x 1) (Zls.unifU k) c1 :=
  fun _ _ _ _ _ N _ _ _ π hs hi _ _ d hd _ _ μ w hw hμ => exists_constituent N π hs hi d hd μ w hw hμ

end Local

end GlobalTheory.CompanionTheory.JacExp

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetSubLeftOfAdmissible
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.JacquetLeft

open GlobalTheory.SmGL.CuspMax GlobalTheory.JacMinCusp Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem tmul_ne_zero' {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] {x : X} {y : Y}
    (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[ℂ] y ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.DYha2.main hx hy

theorem isCuspidal_of_jacquet_min_left {n a b : ℕ} {V W W' : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] [Nontrivial W']
    (π : Representation ℂ (GL (Fin n) k) V) (h : a + b = n)
    (hmin : ∀ (c d : ℕ) (h' : c + d = n), 0 < c → c < a →
      Subsingleton (Jacquet π (unipRad k (two (stdSum h')))))
    (σ : Representation ℂ (GL (Fin a) k) W) (ρ : Representation ℂ (GL (Fin b) k) W') (hσ : IsSmooth σ)
    (φ : (jac₂ (stdSum h) π).IntertwiningMap (extTensor σ ρ)) (hφ : Function.Surjective φ) :
    IsCuspidal σ := by
  refine (isCuspidal_iff_maximal k a W σ).2 ⟨hσ, fun r t h' hr ht => ?_⟩
  have hcd : r + (t + b) = n := by omega
  have hJ : twKer π (unipRad k (two (stdSum hcd))) 1 = ⊤ :=
    Submodule.Quotient.subsingleton_iff.1 (hmin r (t + b) hcd hr (by omega))
  set K' := twKer σ (unipRad k (two (stdSum h'))) 1 with hK'
  set Kab := twKer π (unipRad k (two (stdSum h))) 1 with hKab
  let T : W ⊗[ℂ] W' →ₗ[ℂ] (W ⧸ K') ⊗[ℂ] W' := LinearMap.rTensor W' K'.mkQ
  let Φ : V →ₗ[ℂ] (W ⧸ K') ⊗[ℂ] W' := T ∘ₗ φ.toLinearMap ∘ₗ Kab.mkQ
  have hΦ : ∀ v, Φ v = T (φ (Submodule.Quotient.mk v)) := fun v => rfl

  have hA : ∀ u' ∈ unipRad k (two (stdSum h')), ∀ y : W ⊗[ℂ] W',
      T (extTensor σ ρ (u', 1) y) = T y := by
    intro u' hu' y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul w w' =>
      rw [extTensor_tmul]
      simp only [T, LinearMap.rTensor_tmul, map_one, Module.End.one_apply, Submodule.mkQ_apply]
      congr 1
      exact (Submodule.Quotient.eq K').2 (Submodule.subset_span ⟨⟨u', hu'⟩, w, by simp⟩)
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

  have hB : ∀ g : GL (Fin a) k × GL (Fin b) k, GeneralLinearGroup.det g.1 = 1 → g.2 = 1 → ∀ v : V,
      jac₂ (stdSum h) π g (Submodule.Quotient.mk v) =
        Submodule.Quotient.mk (π (leviEmb k (two (stdSum h)) (leviTwo k _ _ g)) v) := by
    intro g h1 h2 v
    have hd : deltaHalf k (Two (Fin a) (Fin b)) (leviTwo k _ _ g) = 1 := by
      rw [deltaHalf_two, h1, h2]; simp
    show GlobalTheory.SmGL.jac (two (stdSum h)) π (leviTwo k _ _ g) _ = _
    rw [jac_mk, hd]; simp
  have hN : ∀ u ∈ unipRad k (two (stdSum h)), ∀ v : V,
      (Submodule.Quotient.mk (π u v) : V ⧸ Kab) = Submodule.Quotient.mk v := by
    intro u hu v
    exact (Submodule.Quotient.eq Kab).2 (Submodule.subset_span ⟨⟨u, hu⟩, v, by simp⟩)
  have hC : ∀ u ∈ unipRad k (two (stdSum hcd)), ∀ v : V, Φ (π u v) = Φ v := by
    intro u hu v
    have hu' := (mem_unipRad_two_iff hcd).1 hu
    have hp : u ∈ parab k (two (stdSum h)) := by
      rw [mem_parab]
      intro i j hij
      rw [blk_two_stdSum_lt] at hij
      rw [hu' i j (by omega), Matrix.one_apply_ne]
      intro hij'; subst hij'; omega
    obtain ⟨n', hn', hun⟩ := exists_levi_mul_unip k (two (stdSum h)) ⟨u, hp⟩
    set g := (leviTwo k (Fin a) (Fin b)).symm (leviProj k (two (stdSum h)) ⟨u, hp⟩) with hg
    have hlg : leviTwo k _ _ g = leviProj k (two (stdSum h)) ⟨u, hp⟩ := by simp [g]
    have hg2 : g.2 = 1 := by
      ext i j
      show (leviProj k (two (stdSum h)) ⟨u, hp⟩ true : Matrix (Fin b) (Fin b) k) i j = _
      rw [leviProj_apply, two_true, two_true]
      rw [hu' _ _ (by simp; omega)]
      simp [Matrix.one_apply, stdSum]
    have hg1 : g.1 ∈ unipRad k (two (stdSum h')) := by
      rw [mem_unipRad_two_iff]
      intro i j hij
      show (leviProj k (two (stdSum h)) ⟨u, hp⟩ false : Matrix (Fin a) (Fin a) k) i j = _
      rw [leviProj_apply, two_false, two_false]
      rw [hu' _ _ (by simp; omega)]
      simp [Matrix.one_apply, stdSum]
    have hdet : GeneralLinearGroup.det g.1 = 1 := det_eq_one_of_mem_unipRad k hg1
    have hu_eq : u = leviEmb k (two (stdSum h)) (leviTwo k _ _ g) * n' := by rw [hlg]; exact hun
    rw [hu_eq, map_mul, Module.End.mul_apply, hΦ, ← hB g hdet hg2, φ.isIntertwining,
      show g = (g.1, 1) from Prod.ext rfl hg2, hA _ hg1, hN _ hn', ← hΦ]

  have hΦ0 : ∀ v, Φ v = 0 := by
    intro v
    have hv : v ∈ twKer π (unipRad k (two (stdSum hcd))) 1 := hJ ▸ Submodule.mem_top
    have : twKer π (unipRad k (two (stdSum hcd))) 1 ≤ LinearMap.ker Φ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, w, rfl⟩
      simp [hC u u.2 w]
    exact this hv
  have hsurj : Function.Surjective Φ :=
    (LinearMap.rTensor_surjective W' (Submodule.mkQ_surjective K')).comp
      (hφ.comp (Submodule.mkQ_surjective Kab))

  show Subsingleton (W ⧸ K')
  refine ⟨fun x y => ?_⟩
  rw [← sub_eq_zero]
  by_contra hq
  obtain ⟨w, hw⟩ := exists_ne (0 : W')
  obtain ⟨v, hv⟩ := hsurj ((x - y) ⊗ₜ w)
  exact tmul_ne_zero' hq hw (hv.symm.trans (hΦ0 v))

theorem nontrivial_jacquet_top {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (hπ : π.IsIrreducible) (h : n + 0 = n) :
    Nontrivial (Jacquet π (unipRad k (two (stdSum h)))) := by
  have key : ∀ x, GlobalTheory.SmGL.blk (two (stdSum h)) x = false := by
    intro x
    unfold GlobalTheory.SmGL.blk
    obtain ⟨⟨b, y⟩, hy⟩ : ∃ p, (two (stdSum h)).symm x = p := ⟨_, rfl⟩
    rw [hy]
    cases b
    · rfl
    · exact Fin.elim0 y
  have hbot : unipRad k (two (stdSum h)) = ⊥ := by
    by_contra hne
    obtain ⟨i, j, hij⟩ := (GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff).1 hne
    rw [key i, key j] at hij
    exact lt_irrefl _ hij
  have hker : twKer π (⊥ : Subgroup (GL (Fin n) k)) 1 = ⊥ := by
    unfold twKer
    rw [Submodule.span_eq_bot]
    rintro w ⟨⟨g, hg⟩, v, rfl⟩
    rw [Subgroup.mem_bot] at hg
    subst hg
    simp
  haveI : Nontrivial V := GlobalTheory.JacFactor.nontrivial_of_isIrreducible hπ
  rw [hbot]
  show Nontrivial (V ⧸ twKer π ⊥ 1)
  rw [hker]
  exact (Submodule.quotEquivOfEqBot (⊥ : Submodule ℂ V) rfl).toEquiv.nontrivial

theorem bernsteinZelevinsky (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness := fun k _ _ _ _ =>
  ⟨GlobalTheory.BZBridge.irreducibleAdmissible hA k, GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k,
    GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k, GlobalTheory.SmGL.IndDual.inductionContragredient k⟩

theorem exists_quotient_jac₂ (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {n : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible)
    (hn : 0 < n) :
    ∃ (a b : ℕ) (h : a + b = n) (s : IrrRep (GL (Fin a) k)) (t : IrrRep (GL (Fin b) k)),
      0 < a ∧ IsCuspidal s.ρ ∧
        ∃ φ : (jac₂ (stdSum h) π).IntertwiningMap (extTensor s.ρ t.ρ), Function.Surjective φ := by
  classical
  let P : ℕ → Prop := fun d => 0 < d ∧ ∃ (t : ℕ) (h : d + t = n),
    Nontrivial (Jacquet π (unipRad k (two (stdSum h))))
  have hP : ∃ d, P d := ⟨n, hn, 0, rfl, nontrivial_jacquet_top π hi _⟩
  obtain ⟨ha, b, h, hJ⟩ := Nat.find_spec hP
  have hmin : ∀ (c d : ℕ) (h' : c + d = n), 0 < c → c < Nat.find hP →
      Subsingleton (Jacquet π (unipRad k (two (stdSum h')))) := fun c d h' hc hca => by
    by_contra hns
    exact Nat.find_min hP hca ⟨hc, d, h', not_subsingleton_iff_nontrivial.1 hns⟩
  generalize Nat.find hP = a at ha h hJ hmin
  have hBZ := bernsteinZelevinsky hA
  have hfl : HasFiniteLength (GlobalTheory.SmGL.jac (two (stdSum h)) π) :=
    (hBZ k).2.1 _ _ _ (two (stdSum h)) V π hs (hasFiniteLength_of_isIrreducible hi)
  obtain ⟨Y, _, _, τ, hτs, hτi, q, hq⟩ :=
    IrrQuot.exists_irreducible_smooth_quotient _ (isSmooth_jac (two (stdSum h)) hs) hfl hJ
  obtain ⟨s, ⟨E⟩⟩ := GlobalTheory.LeviFactor.exists_equiv_piTensor_levi hBZ k Bool (Two (Fin a) (Fin b))
    (⟨Y, τ, hτs, hτi⟩ : IrrRep _)
  let F : ∀ j : Bool, Representation ℂ (GL (Two (Fin a) (Fin b) j) k) (s j).V := fun j => (s j).ρ
  let B := GlobalTheory.JacFactor.piTensorBoolEquiv F
  let φ : (jac₂ (stdSum h) π).IntertwiningMap (extTensor (F false) (F true)) :=
    ⟨B.toLinearEquiv.toLinearMap ∘ₗ E.toLinearEquiv.toLinearMap ∘ₗ q.toLinearMap, fun g =>
      LinearMap.ext fun v => by
        show B (E (q (GlobalTheory.SmGL.jac (two (stdSum h)) π (leviTwo k _ _ g) v))) =
          extTensor (F false) (F true) g (B (E (q v)))
        have e1 : E (τ (leviTwo k _ _ g) (q v)) = piTensor F (leviTwo k _ _ g) (E (q v)) :=
          E.toIntertwiningMap.isIntertwining _ _ _ _
        have e2 := B.toIntertwiningMap.isIntertwining _ _ g (E (q v))
        rw [q.isIntertwining]
        exact (congrArg B e1).trans e2⟩
  have hφ : Function.Surjective φ :=
    B.toLinearEquiv.surjective.comp (E.toLinearEquiv.surjective.comp hq)
  haveI : Nontrivial (s true).V := GlobalTheory.JacFactor.nontrivial_of_isIrreducible (s true).irr
  exact ⟨a, b, h, s false, s true, ha,
    isCuspidal_of_jacquet_min_left π h hmin (s false).ρ (s true).ρ (s false).smooth φ hφ, φ, hφ⟩

theorem exists_injective_comp {G A B C : Type} [Group G] [AddCommMonoid A] [Module ℂ A] [AddCommMonoid B] [Module ℂ B]
    [AddCommMonoid C] [Module ℂ C] {ρ₁ : Representation ℂ G A} {ρ₂ : Representation ℂ G B}
    {ρ₃ : Representation ℂ G C} (ψ : ρ₁.IntertwiningMap ρ₂) (hψ : Function.Injective ψ) (E : ρ₂.Equiv ρ₃) :
    ∃ f : ρ₁.IntertwiningMap ρ₃, Function.Injective f :=
  ⟨E.toIntertwiningMap.comp ψ, E.toLinearEquiv.injective.comp hψ⟩


set_option maxHeartbeats 4000000 in
theorem exists_embedding_of_prod₂ {a b : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (a + b)) k) V) (s : IrrRep (GL (Fin a) k)) (t : IrrRep (GL (Fin b) k))
    (ha : 0 < a) (hc : IsCuspidal s.ρ) (ψ : π.IntertwiningMap (prod₂ s.ρ t.ρ)) (hψ : Function.Injective ψ) :
    ∃ (y : Fin 2 → IrrGL (k := k)) (hd : ∑ a, (y a).1 = a + b), (y 0).IsCusp ∧
      ∃ f : π.IntertwiningMap (prodIrr y hd), Function.Injective f := by
  have hd : ∑ i, (![IrrGL.of s.ρ s.smooth s.irr, IrrGL.of t.ρ t.smooth t.irr] i).1 = a + b :=
    Fin.sum_univ_two _
  obtain ⟨E⟩ := nonempty_prod₂_equiv_prodIrr s.ρ s.smooth s.irr t.ρ t.smooth t.irr hd
  obtain ⟨f, hf⟩ := exists_injective_comp ψ hψ E
  exact ⟨_, hd, IrrGL.isCusp_of.2 ⟨ha, hc⟩, f, hf⟩

theorem exists_embedding {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSmooth π)
    (hi : π.IsIrreducible) (hn : 0 < n) :
    ∃ (y : Fin 2 → IrrGL (k := k)) (hd : ∑ a, (y a).1 = n), (y 0).IsCusp ∧
      ∃ f : π.IntertwiningMap (prodIrr y hd), Function.Injective f := by
  obtain ⟨a, b, rfl, s, t, ha, hc, φ, hφ⟩ := exists_quotient_jac₂ hA π hs hi hn
  haveI : Nontrivial s.V := GlobalTheory.JacFactor.nontrivial_of_isIrreducible s.irr
  haveI : Nontrivial t.V := GlobalTheory.JacFactor.nontrivial_of_isIrreducible t.irr
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    obtain ⟨w, hw⟩ := exists_ne (0 : s.V)
    obtain ⟨w', hw'⟩ := exists_ne (0 : t.V)
    obtain ⟨v, hv⟩ := hφ (w ⊗ₜ w')
    exact tmul_ne_zero' hw hw' hv.symm
  exact (GlobalTheory.CompanionTheory.Frob.exists_injective_of_jac₂ k a b V s.V t.V π s.ρ t.ρ hs hi φ hφ0).elim fun ψ hψ =>
    exists_embedding_of_prod₂ π s t ha hc ψ hψ

theorem jacquetSubLeft : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → JacquetSubLeft k :=
  fun hA x hx => exists_embedding hA x.rep x.2.rep.smooth x.2.rep.irr hx

end GlobalTheory.CompanionTheory.JacquetLeft

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductPreservesSubquotientStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_preserves_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ} (N : Fin d → ℕ) (M : ℕ) (hM : ∑ i, N i = M) (X Y : Fin d → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)] (ρ : ∀ i, Representation ℂ (GL (Fin (N i)) k) (X i)) (ρ' : ∀ i, Representation ℂ (GL (Fin (N i)) k) (Y i)), (∀ i, IsSmooth (ρ' i)) → (∀ i, IsSubquotient (ρ i) (ρ' i)) → IsSubquotient (multiProd (stdBlocks N hM) ρ) (multiProd (stdBlocks N hM) ρ') := by
  first | exact @GlobalTheory.CompanionTheory.GenMulti.multiProd_isSubquotient_of_forall | exact GlobalTheory.CompanionTheory.GenMulti.multiProd_isSubquotient_of_forall | (intros; apply GlobalTheory.CompanionTheory.GenMulti.multiProd_isSubquotient_of_forall <;> assumption)
end

