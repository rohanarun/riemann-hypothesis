module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdemNotMemFilVOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockCharactersCrystallineOfRules
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0424
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0359
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0414
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0415
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CycZpowCrysDRJump
section
noncomputable section

namespace GlobalTheory.CycPow

open _root_.Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F) {LL : Type} [Field LL] [Algebra Qp LL]

theorem step (u : F) (hu : PD.ι PD.t * u = 1) (hu' : u ∈ PD.Fil (-1)) (n : ℤ) :
    finrank LL ↥(DdR PD (charRep (cycLL PD LL ^ (n + 1)))) =
        finrank LL ↥(DdR PD (charRep (cycLL PD LL ^ n))) ∧
      ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), finrank LL ↥(FildR PD (charRep (cycLL PD LL ^ (n + 1))) τ (a - 1)) =
        finrank LL ↥(FildR PD (charRep (cycLL PD LL ^ n)) τ a) := by
  have htw : IsTwistRep (cycLL PD LL) (charRep (cycLL PD LL ^ n)) (charRep (cycLL PD LL ^ (n + 1))) := by
    refine ⟨LinearEquiv.refl LL LL, fun g x => ?_⟩
    rw [zpow_add_one]
    change (((cycLL PD LL ^ n) g * cycLL PD LL g : LLˣ) : LL) * x =
      ((cycLL PD LL g : LLˣ) : LL) * ((((cycLL PD LL ^ n) g : LLˣ) : LL) * x)
    rw [Units.val_mul]
    ring
  obtain ⟨Φ, hD, hF⟩ := GlobalTheory.DRFil.exists_twist_equiv PD _ _ htw u hu hu'
  exact ⟨by rw [← hD, LinearEquiv.finrank_map_eq], fun τ a => by rw [← hF, LinearEquiv.finrank_map_eq]⟩

theorem isDR_and_finrank [CharZero Qp] [FiniteDimensional Qp LL] (u : F) (hu : PD.ι PD.t * u = 1)
    (hu' : u ∈ PD.Fil (-1)) (k : ℤ) :
    IsDR PD (charRep (cycLL PD LL ^ k)) ∧ ∀ (τ : K →ₐ[Qp] LL) (a : ℤ),
      finrank LL ↥(FildR PD (charRep (cycLL PD LL ^ k)) τ a) = if a ≤ -k then 1 else 0 := by
  induction k using Int.induction_on with
  | zero =>
    have h1 : charRep (1 : G →* LLˣ) = Representation.trivial LL G LL := by
      ext g
      simp [charRep]
    rw [zpow_zero, h1, neg_zero]
    exact ⟨GlobalTheory.CrysExt.isDR_trivial PD, GlobalTheory.CrysExt.finrank_fildR_trivial PD⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := step PD (LL := LL) u hu hu' n
    refine ⟨h1.trans ih.1, fun τ a => ?_⟩
    have h3 := h2 τ (a + 1)
    rw [add_sub_cancel_right] at h3
    rw [h3, ih.2]
    exact if_congr (by omega) rfl rfl
  | pred n ih =>
    obtain ⟨h1, h2⟩ := step PD (LL := LL) u hu hu' (-(n : ℤ) - 1)
    rw [sub_add_cancel] at h1 h2
    refine ⟨h1.symm.trans ih.1, fun τ a => ?_⟩
    rw [← h2, ih.2]
    exact if_congr (by omega) rfl rfl

end Generic

theorem cyc_zpow_crys_dR_jump : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (k : ℤ), IsCrys (P.PD K) (charRep (cycLL (P.PD K) ↥LL.1 ^ k)) ∧ IsDR (P.PD K) (charRep (cycLL (P.PD K) ↥LL.1 ^ k)) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), multV (P.PD K) (charRep (cycLL (P.PD K) ↥LL.1 ^ k)) τ a = if a = -k then 1 else 0 := by
  intro l _ P AI T K LL k
  have := LL.2
  obtain ⟨u, hu', hu⟩ := ((GlobalTheory.MemLoc.TiedUnif.tied_uniformiser l P AI T).2.2 K (-1) 1).1
    (by rw [neg_add_cancel]; exact (P.PD K).one_mem)
  have ht : (P.PD K).ι (P.PD K).t * u = 1 := by
    rw [P.PD_ι, P.period_datum_t_eq]
    exact hu.symm
  obtain ⟨h1, h2⟩ := isDR_and_finrank (P.PD K) (LL := ↥LL.1) u ht hu' k
  refine ⟨GlobalTheory.BlockCrys.isCrys_cyc_zpow _ k, h1, fun τ a => ?_⟩
  rw [multV, h2, h2]
  split_ifs <;> first | rfl | omega

end GlobalTheory.CycPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DDeRhamEqDCrisOfUnramified
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.FontaineAdmissibility

theorem intersectionNumber_baseChange : ∀ D : D7, Formalism.MainNotions.TruncatedSeriesCountingBounds.adm15 D :=
  fun D l _ K LL hb V _ _ _ _ _ ρ _ _ _ hc =>
    GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR l (D.loc l) (D.locA l) (D.locT l) K LL hb V ρ hc

end GlobalTheory.FontaineAdmissibility
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DcrisStrictHodgeFiltrationUnramified
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.Per.CrisStrict

section Abstract

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem ιV_map (f : V →ₗ[LL] V') (x : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V') (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) x) =
      AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) (ιV PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul v b => simp [ιV]

theorem map_mem_Dcris (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V')
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) {x : V ⊗[Qp] B} (hx : x ∈ Dcris PD ρ) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) x ∈ Dcris PD ρ' := by
  have key : ∀ (g : G) (z : V ⊗[Qp] B), actVB PD ρ' g (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) z) =
      AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) (actVB PD ρ g z) := by
    intro g z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul v b => simp [actVB, hf]
  rw [GlobalTheory.Per.CrisDR.mem_Dcris_iff] at hx ⊢
  intro g
  rw [key, hx g]

theorem map_mem_FilV (f : V →ₗ[LL] V') {a : ℤ} {x : V ⊗[Qp] BdR} (hx : x ∈ FilV PD (LL := LL) (V := V) a) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x ∈ FilV PD (LL := LL) (V := V') a := by
  obtain ⟨z, rfl⟩ := hx
  refine ⟨AlgebraTensorModule.map f (LinearMap.id) z, ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul v b => simp

theorem map_map_id {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']
    (f : V →ₗ[LL] V') (g : V' →ₗ[LL] V'') (x : V ⊗[Qp] BdR) :
    AlgebraTensorModule.map g (LinearMap.id : BdR →ₗ[Qp] BdR)
      (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x) =
      AlgebraTensorModule.map (g ∘ₗ f) (LinearMap.id : BdR →ₗ[Qp] BdR) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul v b => simp

theorem mem_FilV_of_injective (f : V →ₗ[LL] V') (hi : Function.Injective f) {a : ℤ} {x : V ⊗[Qp] BdR}
    (hx : AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x ∈ FilV PD (LL := LL) (V := V') a) :
    x ∈ FilV PD (LL := LL) (V := V) a := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f (LinearMap.ker_eq_bot.2 hi)
  have := map_mem_FilV PD g hx
  rwa [map_map_id, hg, AlgebraTensorModule.map_id, LinearMap.id_apply] at this

end Abstract

theorem dcris_strict : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), Function.Bijective (algebraMap ↥(K0 K) ↥K.1) → ∀ (V₁ : Type) [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₁] (ρ₁ : Representation ↥LL.1 ↥(GK K) V₁) (V₂ : Type) [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂] [FiniteDimensional ↥LL.1 V₂] (ρ₂ : Representation ↥LL.1 ↥(GK K) V₂) (π : V₁ →ₗ[↥LL.1] V₂), (∀ g x, π (ρ₁ g x) = ρ₂ g (π x)) → (Function.Surjective π → IsCrys (P.PD K) ρ₁ → ∀ a : ℤ, (FilCris (P.PD K) ρ₁ a).map (AlgebraTensorModule.map π (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B)) = FilCris (P.PD K) ρ₂ a) ∧ (Function.Injective π → ∀ a : ℤ, ∀ y ∈ Dcris (P.PD K) ρ₁, AlgebraTensorModule.map π (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B) y ∈ FilCris (P.PD K) ρ₂ a → y ∈ FilCris (P.PD K) ρ₁ a) := by
  intro l _ P AI T K LL hb V₁ _ _ _ _ _ ρ₁ V₂ _ _ _ _ _ ρ₂ π hπ
  refine ⟨fun hs hc a => le_antisymm ?_ ?_, fun hi a y hy hF => ?_⟩
  · rintro _ ⟨x, ⟨hxD, hxF⟩, rfl⟩
    refine ⟨map_mem_Dcris (P.PD K) ρ₁ ρ₂ π hπ hxD, Submodule.mem_comap.2 ?_⟩
    rw [ιV_map]
    exact map_mem_FilV (P.PD K) π (Submodule.mem_comap.1 hxF)
  · rintro y ⟨hyD, hyF⟩
    have hc2 := ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l P AI T K LL V₁ ρ₁ V₂ ρ₂ π hπ).2 hs hc).1
    have hyR : ιV (P.PD K) (LL := ↥LL.1) (V := V₂) y ∈ DdR (P.PD K) ρ₂ := by
      rw [← (GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR l P AI T K LL hb V₂ ρ₂ hc2).1]
      exact Submodule.mem_map_of_mem hyD
    have hdr1 := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI T K LL V₁ ρ₁ hc).1
    obtain ⟨x', ⟨hx'D, hx'F⟩, hx'⟩ :=
      ((GlobalTheory.DRSubQuot.deRham_sub_quot l P AI T K LL V₁ ρ₁ V₂ ρ₂ π hπ).2 hs hdr1).2 a _ ⟨hyR, hyF⟩
    rw [← (GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR l P AI T K LL hb V₁ ρ₁ hc).1] at hx'D
    obtain ⟨x, hx, rfl⟩ := hx'D
    refine ⟨x, ⟨hx, hx'F⟩, ?_⟩
    apply GlobalTheory.Per.DdREqDcris.ιV_injective (P.PD K) (LL := ↥LL.1)
    rw [ιV_map, hx']
  · refine ⟨hy, ?_⟩
    have h2 := Submodule.mem_comap.1 hF.2
    rw [ιV_map] at h2
    exact Submodule.mem_comap.2 (mem_FilV_of_injective (P.PD K) π hi h2)

end GlobalTheory.Per.CrisStrict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamExistsHodgeTateEigenbasis
section
noncomputable section

namespace GlobalTheory.HTBasis
open _root_.Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_dR_frame : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K LL : FinExt l) (m : ℕ) (r' : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1),
    Module.finrank ↥LL.1 ↥(DdR (P.PD K) (repOf r')) = Module.finrank ℚ_[l] ↥K.1 * m →
    ∀ τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, (∀ x : ↥K.1, ((τ' x : ↥LL.1) : Om l) = (x : Om l)) →
    ∃ (u : Fin m → Fin m → P.R.BdR) (k : Fin m → ℤ),
      (∀ a : ℤ, ((Multiset.map k Finset.univ.val).count a : ℤ) = multV (P.PD K) (repOf r') τ' a) ∧
      (∀ i j, u i j ∈ (P.PD K).Fil (k i)) ∧
      (∀ g : ↥(GK K), (∀ x ∈ LL.1, (g : GQ l) x = x) → ∀ i,
        ((r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (embF P LL)).mulVec
          (fun j => P.actQdR (g : GQ l) (u i j)) = u i) ∧
      (∀ (n : ℤ) (y : Fin m → P.R.BdR), (∀ j, y j ∈ (P.PD K).Fil n) →
        ∃ f : Fin m → P.R.BdR, (∀ i, f i ∈ (P.PD K).Fil (n - k i)) ∧ y = ∑ i, f i • u i) ∧
      LinearIndependent P.R.BdR u := by
  intro l _ P AI T K LL m r' hdR τ' hτ
  haveI := K.2
  haveI := LL.2
  have hDR : IsDR (P.PD K) (repOf r') := by
    unfold IsDR
    rw [hdR, Module.finrank_fin_fun]
  haveI hfinD : FiniteDimensional ↥LL.1 ↥(DdR (P.PD K) (repOf r')) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · haveI : Subsingleton ((Fin 0 → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR) := ⟨fun x y => by
        have h : ∀ z : (Fin 0 → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR, z = 0 := fun z => by
          induction z using TensorProduct.induction_on with
          | zero => rfl
          | tmul v b => rw [Subsingleton.elim v 0, TensorProduct.zero_tmul]
          | add a b ha hb => rw [ha, hb, add_zero]
        rw [h x, h y]⟩
      infer_instance
    · exact Module.finite_of_finrank_pos (by rw [hdR]; exact Nat.mul_pos Module.finrank_pos hm)
  obtain ⟨m', d, k, had⟩ := GlobalTheory.DRFil.exists_adapted (P.PD K) (GlobalTheory.DRFil.isField_dR T) (repOf r')
    (GlobalTheory.DRFil.filSpans T K LL (repOf r') hDR) τ'
  let u' : Fin m' → Fin m → P.R.BdR := fun i => coordF P LL m (d i)
  have hspan' : ∀ (n : ℤ) (y : Fin m → P.R.BdR), (∀ j, y j ∈ (P.PD K).Fil n) →
      ∃ f : Fin m' → P.R.BdR, (∀ i, f i ∈ (P.PD K).Fil (n - k i)) ∧ y = ∑ i, f i • u' i := by
    intro n y hy
    have hY : (∑ j, (Pi.single j 1 : Fin m → ↥LL.1) ⊗ₜ[ℚ_[l]] y j) ∈
        FilV (P.PD K) (LL := ↥LL.1) (V := Fin m → ↥LL.1) n :=
      Submodule.sum_mem _ fun j _ => GlobalTheory.DRFil.tmul_mem_FilV (P.PD K) _ (hy j)
    have hcY : coordF P LL m (∑ j, (Pi.single j 1 : Fin m → ↥LL.1) ⊗ₜ[ℚ_[l]] y j) = y := by
      funext j'
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, Finset.sum_apply, Pi.single_apply]
    obtain ⟨r, hr, he⟩ := had.span n _ hY
    refine ⟨fun i => mulF P LL (r i), fun i => mulF_mem_fil P LL K (hr i), ?_⟩
    have e1 := coordF_sm P LL m (GlobalTheory.DRFil.idem P.R.BdR τ')
      (∑ j, (Pi.single j 1 : Fin m → ↥LL.1) ⊗ₜ[ℚ_[l]] y j)
    rw [mulF_idem P LL K τ' hτ, one_smul, hcY] at e1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e1, he, map_sum]
    exact Finset.sum_congr rfl fun i _ => coordF_sm P LL m (r i) (d i)
  have htop : ⊤ ≤ Submodule.span P.R.BdR (Set.range u') := by
    rintro y -
    choose f hf using fun j => (P.PD K).Fil_exh (y j)
    have hn : ∀ j, y j ∈ (P.PD K).Fil (-(∑ j, |f j|)) := by
      intro j
      have hle : -(∑ j, |f j|) ≤ f j := by
        have h1 : |f j| ≤ ∑ j, |f j| :=
          Finset.single_le_sum (f := fun j => |f j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
        have h2 := neg_abs_le (f j)
        linarith
      exact SetLike.le_def.1 (GlobalTheory.DRFil.fil_antitone (P.PD K) hle) (hf j)
    obtain ⟨c, -, hc⟩ := hspan' _ y hn
    rw [hc]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  letI : Field P.R.BdR := (GlobalTheory.DRFil.isField_dR T).toField
  have hle1 : m ≤ m' := by
    have h1 := finrank_range_le_card (R := P.R.BdR) u'
    rw [Set.finrank, eq_top_iff.2 htop, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at h1
    exact h1
  have hle2 : m' ≤ m := by
    have := GlobalTheory.Per.Components.card_le_of_idem_indep (GlobalTheory.DRFil.idem_mul_idem (F := P.R.BdR) τ')
      (GlobalTheory.DRFil.idem_ne_zero (F := P.R.BdR) τ')
      (fun i j => GlobalTheory.DRFil.ext ℚ_[l] P.R.BdR ((Pi.basisFun ↥LL.1 (Fin m)).coord j) (d i))
      (fun r hr => had.indep r (by
        rw [GlobalTheory.DRFil.eq_sum_basis (Pi.basisFun ↥LL.1 (Fin m))
          (∑ i, GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥LL.1 (Fin m → ↥LL.1) (r i) (d i))]
        refine Finset.sum_eq_zero fun j _ => ?_
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simp only [GlobalTheory.DRFil.ext_sm, GlobalTheory.DRFil.sm_self]
        rw [hr j, map_zero, LinearMap.zero_apply]))
    simpa using this
  obtain rfl : m = m' := le_antisymm hle1 hle2
  have hind : LinearIndependent P.R.BdR u' :=
    linearIndependent_of_top_le_span_of_card_eq_finrank htop (by simp)
  refine ⟨u', k, fun a => ?_, fun i j => coordF_mem_fil P LL m K (had.mem i).2 j, fun g hg i => ?_,
    hspan', hind⟩
  · rw [had.multV_eq a, Multiset.count_map]
    simp [Finset.sum_boole, eq_comm]
    rfl
  · have h1 := coordF_act P LL m K r' g hg (d i)
    rw [((GlobalTheory.DRFil.mem_DdR (P.PD K) (repOf r') (d i)).1 (had.mem i).1.1) g] at h1
    exact h1.symm

end GlobalTheory.HTBasis

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

set_option synthInstance.maxHeartbeats 400000 in
theorem GlobalTheory.HTBasis.htc_basis : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (m : ℕ) (r' : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1), let ρ : Representation ↥LL.1 ↥(GK K) (Fin m → ↥LL.1) := ((Matrix.toLinAlgEquiv' : Matrix (Fin m) (Fin m) ↥LL.1 ≃ₐ[↥LL.1] _) : _ →* _).comp ((Units.coeHom _).comp r'); Module.finrank ↥LL.1 ↥(DdR (P.PD K) ρ) = Module.finrank ℚ_[l] ↥K.1 * m → ∀ τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, (∀ x : ↥K.1, ((τ' x : ↥LL.1) : Om l) = (x : Om l)) → ∀ (K' : FinExt l), K.1 ≤ K'.1 → LL.1 ≤ K'.1 → ∃ (Pm : Matrix.GeneralLinearGroup (Fin m) ℂ_[l]) (k : Fin m → ℤ), (∀ a : ℤ, ((Multiset.map k Finset.univ.val).count a : ℤ) = multV (P.PD K) ρ τ' a) ∧ ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → (r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (fun x => (((x : ↥LL.1) : Om l) : ℂ_[l])) * (Pm : Matrix (Fin m) (Fin m) ℂ_[l]).map (Per.σC (g : GQ l)) = (Pm : Matrix (Fin m) (Fin m) ℂ_[l]) * Matrix.diagonal (fun i => ((((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l])) := by
  intro l _ P AI T K LL m r' ρ hdR τ' hτ K' _hK hL
  obtain ⟨u, k, hcount, hmem, heq, hspan, hind⟩ :=
    GlobalTheory.HTBasis.exists_dR_frame l P AI T K LL m r' hdR τ' hτ
  have hU := GlobalTheory.T.hodgeTateSymbolMatrix_isUnit_det (GlobalTheory.HTBasis.thetaOf T) u k hmem hspan hind
  refine ⟨((Matrix.isUnit_iff_isUnit_det _).2 hU).unit, k, hcount, fun g hg => ?_⟩
  have hfix : ∀ x ∈ LL.1, (g : GQ l) x = x := fun x hx =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x (hL hx)
  exact GlobalTheory.T.hodgeTateSymbolMatrix_equivariant (GlobalTheory.HTBasis.thetaOf T) r' u k hmem g (heq g hfix)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescNEqXPowMulIterateDerivativeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descN_eq_X_pow_mul_iterate_derivative' :
    ∀ (K : Type) [NormedField K] (p : ℕ) (f : K⟦X⟧),
      descN (K := K) p f = X ^ p * (⇑(derivative (R := K)))^[p] f := by
  intro K _ p f
  ext n
  rw [coeff_descN, coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_iterate_derivative, ← Nat.add_descFactorial_eq_ascFactorial, Nat.sub_add_cancel h]
  · rw [Nat.descFactorial_of_lt (Nat.lt_of_not_ge h), Nat.cast_zero, zero_mul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualExponentialImageContainsLattice
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

noncomputable section

namespace GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime]

theorem norm_algebraMap_mul (κ : ℚ_[l]) (α : Om l) :
    ‖algebraMap ℚ_[l] (Om l) κ * α‖ = ‖κ‖ * ‖α‖ := by
  rw [norm_mul, PadicAlgCl.norm_extends]

theorem exists_gen (P : LocPrime l) (K : FinExt l) {s : ℕ} (hs : Lev l s) :
    ∃ g ∈ Gj K s, (P.χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) := by
  have hn : ‖((1 + l ^ s : ℕ) : ℚ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ)) := by
    push_cast
    rw [add_sub_cancel_left, Padic.norm_p_pow]
  have hu : ‖((1 + l ^ s : ℕ) : ℚ_[l])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hs.1
    rw [hk, pow_succ]
    simp
  obtain ⟨g, hg, hχ⟩ := (GlobalTheory.Cyc.finrank_Ks_and_chi_surjective l K).2 P.χQ P.χQ_cyc _ hu
  exact ⟨g, (((GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.2 K g hg).1 s).2 (by rw [hχ, hn]), hχ⟩

theorem expStar_image : ∀ (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), Lev l s → ∀ e : ℕ, ∀ α : Om l, α ∈ Ks K s → ‖α‖ ≤ 1 → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar D.loc (Gj K s) e z ((l : Om l) ^ (betaE l s e) * α) := by
  intro D l _ K s hs e α hα hα1
  obtain ⟨g, hg, hχ⟩ := exists_gen (D.loc l) K hs
  set u : ℚ_[l] := ((1 + l ^ s : ℕ) : ℚ_[l]) with hu
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hlr : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hn : ‖u - 1‖ = (l : ℝ) ^ (-(s : ℤ)) := by
    rw [hu]
    push_cast
    rw [add_sub_cancel_left, Padic.norm_p_pow]
  have hlog : ‖logZl l u‖ = (l : ℝ) ^ (-(s : ℤ)) := by
    rw [(GlobalTheory.PadicLogUnits.logZl_hom l).2.2.2 s hs.1 hs.2 u hn.le, hn]
  have key : ∀ ρ : ℚ_[l], ‖ρ‖ = (l : ℝ) ^ (((e + 1) * (s - 1) : ℕ) - betaE l s e) →
      (∀ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) → ‖(d : Om l)‖ ≤ 1 →
        d - (l : ↥(K0 K)) ^ e * frK (D.loc l) K d = (frK (D.loc l) K ^ s) (∑ a ∈ primeTo l s, lam a) →
        ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar D.loc (Gj K s) e z
          (algebraMap ℚ_[l] (Om l) ρ * cycVal (D.loc l) K s e lam d)) →
      ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧
        ExpStar D.loc (Gj K s) e z ((l : Om l) ^ (betaE l s e) * α) := by
    intro ρ hρ H
    have hρ0 : ρ ≠ 0 := by
      rw [← norm_ne_zero_iff, hρ]
      exact (zpow_pos hlr _).ne'
    set κ : ℚ_[l] := (l : ℚ_[l]) ^ (betaE l s e) / (ρ * (l : ℚ_[l]) ^ ((e + 1) * (s - 1))) with hκ
    have hκ1 : ‖κ‖ = 1 := by
      rw [hκ, norm_div, norm_mul, hρ, Padic.norm_p_zpow, Padic.norm_p_pow, ← zpow_add₀ hlr.ne',
        div_eq_one_iff_eq (zpow_pos hlr _).ne']
      congr 1
      ring
    obtain ⟨lam, d, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_cyclotomicFrobeniusTwistedValue_eq_pow_mul l (D.loc l) K s e hs.1 (algebraMap ℚ_[l] (Om l) κ * α)
      (mul_mem (IntermediateField.algebraMap_mem _ _) hα) (by rw [norm_algebraMap_mul, hκ1, one_mul]; exact hα1)
    obtain ⟨z, hz, hE⟩ := H lam d h1 h2 h3
    refine ⟨z, hz, ?_⟩
    convert hE using 1
    have : ρ * (l : ℚ_[l]) ^ ((e + 1) * (s - 1)) * κ = (l : ℚ_[l]) ^ (betaE l s e) := by
      rw [hκ]
      field_simp
    have h5 := congrArg (algebraMap ℚ_[l] (Om l)) this
    rw [map_mul, map_mul, map_pow, map_zpow₀, map_natCast] at h5
    rw [h4, ← h5]
    ring
  obtain ⟨s', rfl⟩ := Nat.exists_eq_add_of_le' hs.1
  rcases Nat.eq_zero_or_pos e with rfl | he
  · refine key (logZl l u * (((0 : ℕ).factorial : ℚ_[l]) * (l : ℚ_[l]) ^ ((s' + 1) * 0)))⁻¹ ?_ ?_
    · simp only [Nat.factorial_zero, Nat.cast_one, mul_zero, pow_zero, mul_one, norm_inv, hlog, betaE]
      rw [← zpow_neg]
      congr 1
      simp
    · intro lam d h1 h2 h3
      have := _root_.GlobalTheory.ExpImage.expStar_levSum D.loc l (D.locA l) (D.locT l) K (s' + 1) hs 0 g hg hχ ℕ (primeTo l (s' + 1)) lam id
        (fun _ => d) (fun i hi => ⟨h1 i, (Finset.mem_filter.1 hi).2⟩)
        (fun j hj => by
          obtain rfl : j = 0 := Nat.le_zero.1 hj
          exact ⟨h2, by simpa using h3⟩)
      convert this using 5
      simp [cycVal, levSum]
  · refine key _ ?_ (_root_.GlobalTheory.ExpImage.PosWeight.formula_pos D.loc l (D.locA l) (D.locT l) K (s' + 1) hs e he g hg hχ)
    obtain ⟨e', rfl⟩ := Nat.exists_eq_add_of_le' he
    have h6 := GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one l (s' + 1) hs u hn ((e' + 1 : ℕ) : ℤ) (by omega)
    rw [zpow_natCast, padicValInt.of_nat] at h6
    have h7 : ‖(((e' + 1).factorial : ℕ) : ℚ_[l])‖ =
        (l : ℝ) ^ (-((padicValNat l (e' + 1) : ℤ) + (padicValNat l e'.factorial : ℤ))) := by
      rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast (e' + 1).factorial_ne_zero),
        Padic.valuation_natCast, ← Nat.padicValNat_def, Nat.factorial_succ,
        (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.succ_ne_zero _) e'.factorial_ne_zero]
      push_cast
      rfl
    rw [← hu, norm_div, norm_mul, norm_mul, h6, hlog, h7, Padic.norm_p_pow, ← zpow_add₀ hlr.ne',
      ← zpow_add₀ hlr.ne', ← zpow_sub₀ hlr.ne']
    congr 1
    simp only [betaE, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
    push_cast
    have hv : padicValRat l ((e' : ℚ) + 1) = (padicValNat l (e' + 1) : ℤ) := by
      simpa [Nat.add_comm, Nat.padicValNat_def] using (padicValRat_of_nat (p := l) (e' + 1)).symm
    rw [hv]
    ring

end GlobalTheory.ExpImage
end
end

