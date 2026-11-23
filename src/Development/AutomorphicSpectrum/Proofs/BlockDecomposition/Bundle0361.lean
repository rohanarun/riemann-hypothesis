module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.SatakeSocle.SocleOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.GenericPrincipalSeries.GenericPrincipalSeries
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0356
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TemperedProducts.CentredSegSqInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0354
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0352
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOrderedFormSingleRev
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.OneTermOrder

theorem nabs_unifU_lt_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : nabs k (Zls.unifU k) < 1 := by
  rw [nabs_uniformiser (Zls.irreducible_unif (k := k)) (x := Zls.unifU k) rfl]
  have hq : 1 < resCard k := Finite.one_lt_card
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hq)

theorem norm_absPow_natCast (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (t : kˣ) (j : ℕ) :
    ‖((absPow k (j : ℂ) t : ℂˣ) : ℂ)‖ = nabs k t ^ j := by
  rw [val_absPow, Complex.cpow_natCast, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (nabs_pos' k t).le]

theorem isOrderedForm_single_rev : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (ξ : Fin n → kˣ →* ℂˣ) (hξ : ∀ i, IsUnram (ξ i)),
    PositivityTheory.SphericalProduct.AbsAnti (PositivityTheory.SphericalProduct.atUnif k ξ) →
    IsOrderedForm (fun i : Fin n => Segment.single (IrrGL.ofChar (ξ (Fin.rev i))
      (isSmoothChar_of_isUnram (hξ (Fin.rev i)))) (IrrGL.isCusp_ofChar _ _)) (PositivityTheory.SphericalProduct.msOne ξ hξ) := by
  intro k _ _ _ _ n ξ hξ hanti
  refine ⟨?_, fun i j hij hp => ?_⟩
  · have h := Multiset.map_univ_val_equiv (Fin.revPerm (n := n))
    rw [PositivityTheory.SphericalProduct.msOne]
    conv_rhs => rw [← h, Multiset.map_map]
    rfl
  · obtain ⟨-, m, hm, he⟩ := hp
    have he' : IrrGL.ofChar (ξ (Fin.rev j)) (isSmoothChar_of_isUnram (hξ (Fin.rev j))) =
        (IrrGL.ofChar (ξ (Fin.rev i)) (isSmoothChar_of_isUnram (hξ (Fin.rev i)))).nu (m : ℂ) := he
    rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at he'
    have hle : ‖((ξ (Fin.rev i) (Zls.unifU k) : ℂˣ) : ℂ)‖ ≤ ‖((ξ (Fin.rev j) (Zls.unifU k) : ℂˣ) : ℂ)‖ :=
      hanti (Fin.rev_le_rev.2 hij.le)
    rw [he', MonoidHom.mul_apply, Units.val_mul, norm_mul, norm_absPow_natCast] at hle
    have hpos : 0 < ‖((ξ (Fin.rev i) (Zls.unifU k) : ℂˣ) : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
    have hlt : nabs k (Zls.unifU k) ^ m < 1 :=
      pow_lt_one₀ (nabs_pos' k _).le (nabs_unifU_lt_one k) hm.ne'
    nlinarith

end GlobalTheory.CompanionTheory.OneTermOrder
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothSmInd
section
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZFun

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]

theorem isSmooth_smInd (H : Subgroup G) (σ : Representation ℂ H W) : IsSmooth (smInd H σ) := by
  intro f
  have e : {g : G | smInd H σ g f = f} = {g : G | ind H σ g f.1 = f.1} := by
    ext g
    exact Subtype.ext_iff
  rw [e]
  exact f.2

theorem isSmooth_cInd (H : Subgroup G) (σ : Representation ℂ H W) : IsSmooth (cInd H σ) := by
  intro f
  have e : {g : G | cInd H σ g f = f} = {g : G | smInd H σ g f.1 = f.1} := by
    ext g
    exact Subtype.ext_iff
  rw [e]
  exact isSmooth_smInd H σ f.1

end GlobalTheory.CompanionTheory.BZFun
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetCuspidalSupportOfFunctional
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.CharTensor

theorem piTensor_detRep_apply {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (ξ : Fin n → (kˣ →* ℂˣ)) (t : ∀ _ : Fin n, GL (Fin 1) k)
    (y : PiTensorProduct ℂ fun _ : Fin n => ℂ) :
    piTensor (fun a => detRep (Fin 1) (ξ a)) t y = PositivityTheory.Lbc.torusChar ξ t • y := by
  induction y using PiTensorProduct.induction_on with
  | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul_tprod c x =>
    rw [map_smul, piTensor_tprod, PositivityTheory.Lbc.torusChar]
    simp [detRep]
    rw [smul_comm]
    have h := (PiTensorProduct.tprod ℂ).map_smul_univ
      (fun a => (↑(ξ a (Matrix.GeneralLinearGroup.det (t a))) : ℂ)) x
    simpa [smul_eq_mul] using congrArg (fun z => c • z) h

theorem tprod_one_ne_zero (n : ℕ) : PiTensorProduct.tprod ℂ (fun _ : Fin n => (1 : ℂ)) ≠ 0 := by
  intro h
  have h1 := congrArg (PiTensorProduct.constantBaseRingEquiv (Fin n) ℂ) h
  simp at h1

theorem exists_intertwiningMap_piTensor_ofChar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (ξ : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ a, IsSmoothChar (ξ a))
    (hd : ∑ a, (IrrGL.ofChar (ξ a) (hξ a)).1 = n)
    (f : Jacquet π (unipRad k (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd)) →ₗ[ℂ] ℂ) (hf : f ≠ 0)
    (hfe : ∀ t w, f (GlobalTheory.SmGL.jac (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd) π t w) =
      PositivityTheory.Lbc.torusChar ξ t * f w) :
    ∃ g : (GlobalTheory.SmGL.jac (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd) π).IntertwiningMap
        (piTensor fun a => (IrrGL.ofChar (ξ a) (hξ a)).rep), ∃ w, g w ≠ 0 := by
  let E : (piTensor fun a => detRep (Fin 1) (ξ a)).Equiv (piTensor fun a => (IrrGL.ofChar (ξ a) (hξ a)).rep) :=
    piTensorEquiv fun a => equivRep (IrrRep.det (Fin 1) (ξ a) (hξ a))
  let o : PiTensorProduct ℂ (fun _ : Fin n => ℂ) := PiTensorProduct.tprod ℂ fun _ => 1
  let g₀ : (GlobalTheory.SmGL.jac (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd) π).IntertwiningMap
      (piTensor fun a => detRep (Fin 1) (ξ a)) :=
    { toFun := fun w => f w • o
      map_add' := fun v w => by simp [add_smul]
      map_smul' := fun c w => by simp [mul_smul]
      isIntertwining' := fun t => LinearMap.ext fun w => by
        show f (GlobalTheory.SmGL.jac _ π t w) • o = piTensor (fun a => detRep (Fin 1) (ξ a)) t (f w • o)
        rw [hfe]
        exact (mul_smul _ _ _).trans (piTensor_detRep_apply ξ t (f w • o)).symm }
  obtain ⟨w, hw⟩ : ∃ w, f w ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (LinearMap.ext h)
  refine ⟨E.toIntertwiningMap.comp g₀, w, fun h => ?_⟩
  have h1 : E.toLinearEquiv (f w • o) = 0 := h
  rw [LinearEquiv.map_eq_zero_iff] at h1
  exact (smul_ne_zero hw (tprod_one_ne_zero n)) h1

theorem chartotensor : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (ξ : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ a, IsSmoothChar (ξ a)) (hd : ∑ a, (IrrGL.ofChar (ξ a) (hξ a)).1 = n) (f : Jacquet π (unipRad k (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd)) →ₗ[ℂ] ℂ), f ≠ 0 → (∀ t w, f (GlobalTheory.SmGL.jac (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd) π t w) = PositivityTheory.Lbc.torusChar ξ t * f w) → ∃ g : (GlobalTheory.SmGL.jac (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd) π).IntertwiningMap (piTensor fun a => (IrrGL.ofChar (ξ a) (hξ a)).rep), ∃ w, g w ≠ 0 := by
  intro k _ _ _ _ n V _ _ π ξ hξ hd f hf hfe
  exact exists_intertwiningMap_piTensor_ofChar n π ξ hξ hd f hf hfe

end GlobalTheory.CompanionTheory.CharTensor

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleAdmissibleFixed
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.Jacquet

theorem finiteDimensional_fixed_jac :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
      (hd : ∑ _a : Fin n, 1 = n) {V : Type} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin n) k) V), IsAdmissible π → PositivityTheory.Lbc.C0 k → PositivityTheory.Lbc.C3 k →
      ∀ m, 1 ≤ m → FiniteDimensional ℂ ↥(fixed (GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd) π)
        (PositivityTheory.Lbc.KM k n (Zls.Km k n m) (fun _ : Fin n => 1) hd)) := by
  intro k _ _ _ _ n hd V _ _ π hπ h0 h3 m hm
  obtain ⟨hopen, hcompact, hfact⟩ := h0 n m n (fun _ : Fin n => 1) hd hm
  obtain ⟨-, hsurj, -⟩ := h3 n n (fun _ : Fin n => 1) hd (Zls.Km k n m) hopen hcompact hfact
    (fun _ => Nat.one_pos) V π hπ
  haveI : FiniteDimensional ℂ ↥(fixed π (Zls.Km k n m)) := hπ.2 _ hopen hcompact
  let f : ↥(fixed π (Zls.Km k n m)) →ₗ[ℂ]
      Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)) :=
    (Submodule.mkQ _).comp (Submodule.subtype _)
  have hle : fixed (GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd) π)
      (PositivityTheory.Lbc.KM k n (Zls.Km k n m) (fun _ : Fin n => 1) hd) ≤ LinearMap.range f := by
    intro w hw
    obtain ⟨v, hv⟩ := hsurj w hw
    exact ⟨v, hv⟩
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.CompanionTheory.Jacquet
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleEquivFoundation
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.JacquetDict

theorem twKer_one_eq_coinvariantsKer {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (U : Subgroup G) :
    twKer ρ U 1 = Representation.Coinvariants.ker (ρ.comp U.subtype) := by
  unfold GlobalTheory.PRep.twKer Representation.Coinvariants.ker
  congr 1
  ext w
  constructor
  · rintro ⟨n, v, rfl⟩
    exact ⟨(n, v), by simp⟩
  · rintro ⟨⟨n, v⟩, rfl⟩
    exact ⟨n, v, by simp⟩

theorem jacquet_stdBlocks_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), ∃ e : Jacquet π (unipRad k (stdBlocks d hd)) ≃ₗ[ℂ] GroundTheory.Automorphic.Parabolic.JacquetModule k N (Zl.JC.blockIdx d hd) π, (∀ v : V, e (Submodule.Quotient.mk v) = Representation.Coinvariants.mk _ v) ∧ ∀ (g : Levi k (fun a => Fin (d a))) (hg : leviEmb k (stdBlocks d hd) g ∈ GroundTheory.Automorphic.Parabolic.levi k N (Zl.JC.blockIdx d hd)) (x : Jacquet π (unipRad k (stdBlocks d hd))), e (jacU (stdBlocks d hd) π g x) = GroundTheory.Automorphic.Parabolic.jacquetAction k N (Zl.JC.blockIdx d hd) π ⟨_, hg⟩ (e x) := by
  intro k _ _ _ _ N V _ _ π h d hd
  have hPQ := GlobalTheory.CompanionTheory.ParabolicCompare.unipRad_stdBlocks_eq_unipotentRadical k h N d hd
  have hK : twKer π (unipRad k (stdBlocks d hd)) 1 =
      Representation.Coinvariants.ker
        (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N (Zl.JC.blockIdx d hd)).subtype) := by
    rw [hPQ]
    exact twKer_one_eq_coinvariantsKer π _
  refine ⟨Submodule.quotEquivOfEq _ _ hK, ?_, ?_⟩
  · intro v
    rfl
  · intro g hg x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

end GlobalTheory.CompanionTheory.JacquetDict
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetTwoFactorCentralCharacterMul
section
noncomputable section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.JacCentral

theorem subQuot_apply_of_smul {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (S T : Subrepresentation ρ) {g : G} {c : ℂ}
    (h : ∀ v, ρ g v = c • v) (y : S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) :
    subQuot S T g y = c • y := by
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hs : S.toRepresentation g s = c • s := Subtype.ext (h s)
  show Submodule.Quotient.mk (S.toRepresentation g s) = _
  rw [hs, Submodule.Quotient.mk_smul]

theorem exists_step_of_jhMult_ne_zero {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
    (h : jhMult σ ρ ≠ 0) :
    ∃ S T : Subrepresentation ρ, Nonempty ((subQuot S T).Equiv σ) := by
  by_contra hc
  refine h (le_antisymm (iSup₂_le fun r hr => ?_) bot_le)
  rcases Nat.eq_zero_or_pos r with rfl | hpos
  · simp
  · obtain ⟨S, T, -, -, hi⟩ := hr
    exact absurd ⟨S ⟨0, hpos⟩, T ⟨0, hpos⟩, hi ⟨0, hpos⟩⟩ hc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem leviEmb_scalar {s N : ℕ} (d : Fin s → ℕ) (hd : ∑ a, d a = N) (t : kˣ) :
    leviEmb k (stdBlocks d hd) (fun a => Matrix.GeneralLinearGroup.scalar (Fin (d a)) t) =
      Matrix.GeneralLinearGroup.scalar (Fin N) t := by
  apply Units.ext
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks d hd).surjective j
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    simp [Matrix.scalar_apply, Matrix.diagonal_apply]
  · rw [leviEmb_apply_ne k _ _ hab]
    have : (stdBlocks d hd) ⟨a, i⟩ ≠ (stdBlocks d hd) ⟨b, j⟩ := fun h => by
      have := (stdBlocks d hd).injective h
      exact hab (congrArg Sigma.fst this)
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, this]

theorem nabs_det_scalar (n : ℕ) (t : kˣ) :
    nabs k (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin n) t)) =
      nabs k t ^ n := by
  have : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin n) t) = t ^ n := by
    ext; simp [Matrix.GeneralLinearGroup.scalar]
  rw [this]
  simp [nabs]

theorem deltaHalf_scalar (d : Fin 2 → ℕ) (t : kˣ) :
    deltaHalf k (fun a => Fin (d a))
      (fun a => Matrix.GeneralLinearGroup.scalar (Fin (d a)) t) = 1 := by
  have h0 : modExp (fun a => Fin (d a)) (0 : Fin 2) = d 1 := by
    simp [modExp, Finset.sum_filter, Fin.sum_univ_two]
  have h1 : modExp (fun a => Fin (d a)) (1 : Fin 2) = -(d 0 : ℤ) := by
    simp [modExp, Finset.sum_filter, Fin.sum_univ_two]
  have hm : modulus k (fun a => Fin (d a))
      (fun a => Matrix.GeneralLinearGroup.scalar (Fin (d a)) t) = 1 := by
    have hp := (nabs_pos' k t).ne'
    rw [modulus, Fin.prod_univ_two, h0, h1, nabs_det_scalar, nabs_det_scalar, zpow_natCast, zpow_neg,
      zpow_natCast, ← pow_mul, ← pow_mul, mul_comm (d 0) (d 1)]
    exact mul_inv_cancel₀ (pow_ne_zero _ hp)
  apply Units.ext
  rw [val_deltaHalf, hm]
  simp

theorem piTensor_apply_of_smul {h : ℕ} (x : Fin h → IrrGL (k := k)) (g : ∀ a, GL (Fin (x a).1) k)
    (c : Fin h → ℂ) (hc : ∀ a v, (x a).rep (g a) v = c a • v)
    (w : PiTensorProduct ℂ (fun a => (x a).2.rep.V)) :
    piTensor (fun a => (x a).rep) g w = (∏ a, c a) • w := by
  induction w using PiTensorProduct.induction_on with
  | add y z hy hz => rw [map_add (f := _), hy, hz, smul_add]
  | smul_tprod r y =>
    rw [map_smul, piTensor_tprod, smul_comm]
    congr 1
    simp only [hc]
    exact MultilinearMap.map_smul_univ _ _ _

theorem smul_eq_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [Nontrivial W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (E : ρ.Equiv σ) {g : G} {c c' : ℂ} (hρ : ∀ v, ρ g v = c • v) (hσ : ∀ w, σ g w = c' • w) :
    c' = c := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨y, rfl⟩ := E.toLinearEquiv.surjective w
  have hE : E.toIntertwiningMap (ρ g y) = σ g (E.toIntertwiningMap y) :=
    E.toIntertwiningMap.isIntertwining _ _ g y
  rw [hρ, hσ, map_smul] at hE
  have h2 : (c - c') • E.toLinearEquiv y = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact hE
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exact (sub_eq_zero.1 h3).symm
  · exact absurd h3 hw

theorem scalar_mul_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), ∀ (x : Fin 2 → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), Zc.jm x hd π ≠ 0 → ∀ (t : kˣ) (c c0 c1 : ℂ), (∀ v, π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = c • v) → Zl.ScalarBy (x 0) t c0 → Zl.ScalarBy (x 1) t c1 → c0 * c1 = c := by
  intro k _ _ _ _ N V _ _ π x hd hj t c c0 c1 hc h0 h1
  obtain ⟨S, T, ⟨E⟩⟩ := exists_step_of_jhMult_ne_zero (show jhMult (piTensor fun a => (x a).rep)
    (GlobalTheory.SmGL.jac (stdBlocks (fun a => (x a).1) hd) π) ≠ 0 from hj)
  let g : Levi k (fun a => Fin (x a).1) := fun a => Matrix.GeneralLinearGroup.scalar (Fin (x a).1) t
  have hjac : ∀ v, GlobalTheory.SmGL.jac (stdBlocks (fun a => (x a).1) hd) π g v = c • v := by
    intro v
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    rw [jac_mk, show deltaHalf k (fun a => Fin (x a).1) g = 1 from deltaHalf_scalar _ t,
      show leviEmb k (stdBlocks (fun a => (x a).1) hd) g = _ from leviEmb_scalar _ hd t, hc]
    simp [Submodule.Quotient.mk_smul]
  let cc : Fin 2 → ℂ := ![c0, c1]
  have hcc : ∀ a v, (x a).rep (g a) v = cc a • v := by
    intro a v
    fin_cases a
    · exact h0 v
    · exact h1 v
  haveI := GlobalTheory.CompanionTheory.TensorIrr.nontrivial_piTensorProduct_irrGL k x
  have hfin := smul_eq_of_equiv E (subQuot_apply_of_smul S T hjac)
    (piTensor_apply_of_smul x g cc hcc)
  rw [Fin.prod_univ_two] at hfin
  exact hfin

end GlobalTheory.CompanionTheory.JacCentral

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastBlockCentralScalarModulusOneStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.last_block_central_scalar_modulus_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h), j.val + 1 = h → leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) = Matrix.GeneralLinearGroup.scalar (Fin N) t ∧ modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j) = 1 := by
  intro k _ _ _ _ h N d hd t j hj
  open GlobalTheory.CompanionTheory.ZjScalar in
    constructor
    · apply Units.ext
      ext p q
      obtain ⟨⟨a, x⟩, rfl⟩ := (stdBlocks d hd).surjective p
      obtain ⟨⟨b, y⟩, rfl⟩ := (stdBlocks d hd).surjective q
      by_cases hab : a = b
      · subst hab
        rw [leviEmb_apply_same, zj_last d t j hj a]
        by_cases hxy : x = y
        · subst hxy
          simp [Matrix.GeneralLinearGroup.scalar]
        · have : stdBlocks d hd ⟨a, x⟩ ≠ stdBlocks d hd ⟨a, y⟩ := fun e => hxy (by simpa using (stdBlocks d hd).injective e)
          simp [Matrix.GeneralLinearGroup.scalar, hxy, this]
      · have : stdBlocks d hd ⟨a, x⟩ ≠ stdBlocks d hd ⟨b, y⟩ := fun e =>
          hab (congrArg Sigma.fst ((stdBlocks d hd).injective e))
        rw [leviEmb_apply_ne k _ _ hab]
        simp [Matrix.GeneralLinearGroup.scalar, this]
    · have hx : nabs k t ≠ 0 := (nabs_pos' k t).ne'
      simp only [modulus, nabs_det_zj_last d t j hj]
      have : ∀ a, (nabs k t ^ d a) ^ modExp (fun a => Fin (d a)) a =
          nabs k t ^ ((d a : ℤ) * modExp (fun a => Fin (d a)) a) := fun a => by
        rw [zpow_mul, zpow_natCast]
      simp only [this]
      rw [prod_zpow_eq _ _ hx, sum_card_mul_modExp, zpow_zero]
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviRestrictionSmooth
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.CTFin.Slice1
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}


variable (E r s) in
def blockOne (x : Lie E r) : Lie E (r + s) :=
  toL (Matrix.reindex (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
    (Matrix.fromBlocks (Matrix.of x) 0 0 1))

theorem contDiff_blockOne : ContDiff ℝ (⊤ : ℕ∞) (blockOne E r s) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  change ContDiff ℝ _ (fun x : Lie E r => Matrix.fromBlocks (Matrix.of x) 0 0 (1 : Matrix (Fin s) (Fin s) (Cinf E))
    ((GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i) ((GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j))
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'
  rcases i' with i' | i' <;> rcases j' with j' | j'
  · exact contDiff_apply_apply ℝ i' j'
  · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_const

theorem blockOne_val (y : GL (Fin r) (Cinf E)) :
    blockOne E r s (toL (y : Matrix (Fin r) (Fin r) (Cinf E))) =
      toL ((lev (Cinf E) r s (y, 1) : GL _ _) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) := by
  have hv (g : GL (Fin r) (Cinf E) × GL (Fin s) (Cinf E)) :
      (GlobalTheory.SmGL.emb₂ (Cinf E) (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) g).val =
        Matrix.reindex (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
          (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    simp [GlobalTheory.SmGL.emb₂, GlobalTheory.SmGL.leviEmb, GlobalTheory.SmGL.leviTwo,
      GlobalTheory.SmGL.two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i with a | a <;>
      rcases (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j with b | b <;> simp
  rw [lev, hv]
  rfl

theorem exists_val_of_mem_invSet {x : Lie E r} (hx : x ∈ invSet E r) :
    ∃ y : GL (Fin r) (Cinf E), x = toL (y : Matrix (Fin r) (Fin r) (Cinf E)) :=
  ⟨(show IsUnit (Matrix.of x) from hx).unit, rfl⟩

theorem toL_val_mem_invSet (y : GL (Fin r) (Cinf E)) :
    toL (y : Matrix (Fin r) (Fin r) (Cinf E)) ∈ invSet E r :=
  show IsUnit (Matrix.of (Matrix.of.symm (y : Matrix (Fin r) (Fin r) (Cinf E)))) from y.isUnit

theorem sm_lev_slice (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (F : GA E (r + s) → ℂ)
    (hF : F ∈ Sm E (r + s)) : (fun m : GA E r => F (lev (Ad E) r s (m, 1))) ∈ Sm E r := by
  intro g
  have hmaps : Set.MapsTo (blockOne E r s) (invSet E r) (invSet E (r + s)) := by
    intro x hx
    obtain ⟨y, rfl⟩ := exists_val_of_mem_invSet hx
    rw [blockOne_val]
    exact toL_val_mem_invSet _
  have hcomp := (hF (lev (Ad E) r s (g, 1))).comp contDiff_blockOne.contDiffOn hmaps
  refine hcomp.congr fun x hx => ?_
  obtain ⟨y, rfl⟩ := exists_val_of_mem_invSet hx
  rw [Function.comp_apply, blockOne_val, chart_val, chart_val]
  have e1 : lev (Ad E) r s (infGL E r y, 1) = infGL E (r + s) (lev (Cinf E) r s (y, 1)) := by
    rw [← lev_infGL, map_one]
  rw [← e1, lev_mul_one]

end GlobalTheory.CompanionTheory.CTFin.Slice1
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCharacterEq
section
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMir

theorem mirChar_eq_thetaA_single (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : GlobalTheory.BZMir.Fun.MirCharEq k := by
  intro ψ n
  have h : chrV k ψ n = chrA k ψ (Pi.single (Fin.last n) 1) := by
    ext v
    simp [chrV, chrA]
  rw [mirChar, thetaA, h]

end GlobalTheory.CompanionTheory.BZMir
end

