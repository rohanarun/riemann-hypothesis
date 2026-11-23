module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0377
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0576
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0555
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0534
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0530
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0558
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0574
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0531
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0536
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0553
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0475
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisElementMovingTiltedUniformizer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0520
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0483
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0474
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0521
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0556
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0569
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0575

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeBasisFrobeniusEquationDisc
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem mul_eq_smul_one_comm {R : Type} [CommRing R] [IsDomain R] {d : ℕ}
    {M M' : Matrix (Fin d) (Fin d) R} {c : R} (hc : c ≠ 0) (h : M * M' = c • (1 : Matrix (Fin d) (Fin d) R)) :
    M' * M = c • (1 : Matrix (Fin d) (Fin d) R) := by
  have hdet : M.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ hc h1.symm
  have key : M.det • (M' * M) = M.det • (c • (1 : Matrix (Fin d) (Fin d) R)) := by
    calc M.det • (M' * M) = (M.adjugate * M) * (M' * M) := by
          rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
      _ = M.adjugate * (M * M') * M := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.adjugate_mul, smul_comm]
  ext i j
  have h2 := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h2
  simpa [Matrix.smul_apply] using mul_left_cancel₀ hdet h2

theorem eq_zero_of_mul_eq_zero_of_mul_eq_smul {R : Type} [CommRing R] {d : ℕ}
    {W W' M : Matrix (Fin d) (Fin d) R} {t : R} (ht : t ∈ nonZeroDivisors R)
    (h : W * W' = t • (1 : Matrix (Fin d) (Fin d) R)) (hM : W * M = 0) : M = 0 := by
  have hdet : W.det ∈ nonZeroDivisors R := by
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    have htp : t ^ Fintype.card (Fin d) ∈ nonZeroDivisors R := pow_mem ht _
    rw [mem_nonZeroDivisors_iff] at htp ⊢
    refine ⟨fun x hx => htp.1 x (by rw [← h1, mul_comm W.det, mul_assoc, hx, mul_zero]),
      fun x hx => htp.2 x (by rw [← h1, ← mul_assoc, hx, zero_mul])⟩
  have key : W.det • M = 0 := by
    rw [← Matrix.one_mul M, ← Matrix.smul_mul, ← Matrix.adjugate_mul, Matrix.mul_assoc, hM, Matrix.mul_zero]
  ext i j
  have h2 := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h2 ⊢
  exact (mem_nonZeroDivisors_iff.1 hdet).1 _ h2

theorem map_smul_ringHom {R R' : Type} [CommRing R] [CommRing R'] {m n : Type} (f : R →+* R') (c : R)
    (M : Matrix m n R) : (c • M).map f = f c • M.map f := by
  ext i j; simp

end GlobalTheory.BSP

namespace GlobalTheory.BSP

theorem Height.bas_frob : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ Φ : bk.DS bk.ρ₀ →+* bk.DS bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (frobS l bk.a) Φ → ((l : bk.DS bk.ρ₀) ^ s.c₁ * toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E) ^ s.N) • (ht.bas * ht.A.map (toDisc l (X : bk.S) bk.ρ₀)) = toDisc l (X : bk.S) bk.ρ₀ bk.E ^ (ht.a + 2 * s.N) • (s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * ht.bas.map Φ) := by
  intro l _ K bk d ρ τ s ht hτ Φ hΦ
  have hρ : (0 : ℝ≥0) < bk.ρ₀ := by
    unfold BK.ρ₀
    exact NNReal.rpow_pos (Nat.cast_pos.2 (Fact.out : l.Prime).pos)
  have hρ1 : bk.ρ₀ ≤ 1 := by
    unfold BK.ρ₀
    apply NNReal.rpow_le_one_of_one_le_of_nonpos
    · exact_mod_cast (Fact.out : l.Prime).one_lt.le
    · have : (0:ℝ) ≤ 1 / (bk.Ep.natDegree : ℝ) := by positivity
      linarith
  have hev : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 hρ
  have hXl : frobS l bk.a (X : bk.S) = X ^ l := by
    simp [frobS]
  have hfr : ‖toDisc l (bk.ev X) bk.ρ₀ (WittVector.frobenius (bk.ev X))‖ ≤ bk.ρ₀ := by
    rw [← bk.ev_frob, hXl, map_pow]
    refine (norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) l hρ).trans ?_
    exact pow_le_of_le_one (by positivity) (by exact_mod_cast hρ1) (Fact.out : l.Prime).ne_zero
  set i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map bk.ev hev with hi_def
  have hi : IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i := isDiscMap_map _ _
  set ΦA : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map WittVector.frobenius hfr with hΦA_def
  have hΦA : IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius ΦA := isDiscMap_map _ _
  have hcomm : i.comp Φ = ΦA.comp i := by
    have h1 : IsDiscMap (l := _) (u := _) (ρ := _) (bk.ev.comp (frobS l bk.a)) (i.comp Φ) :=
      ⟨fun a => by simp only [RingHom.comp_apply, hΦ.ext, hi.ext], fun x => (hi.norm_le _).trans (hΦ.norm_le _)⟩
    have h2 : IsDiscMap (l := _) (u := _) (ρ := _) (bk.ev.comp (frobS l bk.a)) (ΦA.comp i) := by
      have e : bk.ev.comp (frobS l bk.a) = (WittVector.frobenius : Ainf l →+* Ainf l).comp bk.ev :=
        RingHom.ext bk.ev_frob
      rw [e]
      exact ⟨fun a => by simp only [RingHom.comp_apply, hΦA.ext, hi.ext], fun x => (hΦA.norm_le _).trans (hi.norm_le _)⟩
    exact h1.unique h2
  obtain ⟨ι, ⟨tb⟩⟩ := _root_.GlobalTheory.BSP.AinfTopBasis.main l K bk
  have hinj : Function.Injective i := (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk _ bk.ev ι tb).2.2.2 i hi
  have hlS : (l : bk.S) ∈ nonZeroDivisors bk.S :=
    (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk bk.S (RingHom.id _) Unit (@TopBasis.self _ _ bk.J bk.complete)).2.2.1
  have hτr : bk.iA τ ∈ nonZeroDivisors (bk.DA bk.ρ₀) := _root_.GlobalTheory.BSP.iA_per_mem_nonZeroDivisors l K bk τ hτ
  have hφE : IsUnit (bk.iS (frobS l bk.a bk.E)) := by
    have h := (_root_.GlobalTheory.BSP.isUnit_toDisc_frobS_E l K bk).map i
    rw [hi.ext] at h; exact h
  have hL : IsUnit ((l : ℕ) : bk.DA bk.ρ₀) := isUnit_l_disc l (bk.ev X) bk.ρ₀
  have hiS : ∀ a, i (toDisc l (X : bk.S) bk.ρ₀ a) = bk.iS a := hi.ext
  have hΦiA : ∀ a, ΦA (bk.iA a) = bk.iA (WittVector.frobenius a) := hΦA.ext
  have hΦiS : ∀ a, ΦA (bk.iS a) = bk.iS (frobS l bk.a a) := fun a => by
    simp only [BK.iS, RingHom.comp_apply, hΦiA, bk.ev_frob]
  have hXX : s.X' * s.X = ((l : bk.S) ^ s.c₂ * bk.E ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) bk.S) :=
    mul_eq_smul_one_comm (mul_ne_zero (pow_ne_zero _ (nonZeroDivisors.ne_zero hlS)) (pow_ne_zero _ bk.E_ne_zero)) s.X_mul

  have hmapinj : ∀ M M' : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀), M.map i = M'.map i → M = M' := fun M M' h => by
    ext a b; exact hinj (congrFun (congrFun h a) b)
  apply hmapinj
  have hcomm' : ∀ z, i (Φ z) = ΦA (i z) := RingHom.congr_fun hcomm
  simp only [map_smul_ringHom, Matrix.map_mul, Height.bas, Matrix.map_map, Function.comp_def, hiS, map_mul, map_pow,
    map_natCast, RingHom.comp_apply, hcomm', hΦ.ext]

  set L : bk.DA bk.ρ₀ := ((l : ℕ) : bk.DA bk.ρ₀) with hL_def
  set e : bk.DA bk.ρ₀ := bk.iS bk.E with he_def
  set φe : bk.DA bk.ρ₀ := bk.iS (frobS l bk.a bk.E) with hφe_def
  set XA := s.X.map bk.iS with hXA
  set X'A := s.X'.map bk.iS with hX'A
  set φXA := s.X.map (bk.iS.comp (frobS l bk.a)) with hφXA
  set φX'A := s.X'.map (bk.iS.comp (frobS l bk.a)) with hφX'A
  set FA := s.F.map (bk.iS.comp C) with hFA
  set AA := ht.A.map bk.iS with hAA
  set Zi := ht.Z.map i with hZi
  set ZΦ := ht.Z.map (fun z => ΦA (i z)) with hZΦ
  set YA := ht.Y.map bk.iA with hYA
  have hW : s.W * Zi = YA := ht.W_mul i hi
  have hZΦ' : ZΦ = Zi.map ΦA := by rw [hZΦ, hZi, Matrix.map_map]; rfl
  have hWΦ : s.W.map ΦA * ZΦ = YA.map ΦA := by rw [hZΦ', ← Matrix.map_mul, hW]
  have hP : e ^ ht.a • YA.map ΦA = YA * AA := by
    have h := congrArg (fun M => M.map bk.iA) ht.φ
    simp only [map_smul_ringHom, Matrix.map_mul, Matrix.map_map] at h
    have e1 : YA.map ΦA = ht.Y.map (bk.iA.comp WittVector.frobenius) := by
      rw [hYA, Matrix.map_map]; congr 1; funext x; exact hΦiA x
    rw [e1]; rw [map_pow] at h; exact h
  have hS : L ^ s.c₁ • (s.W.map ΦA * φX'A) = φe ^ s.N • (s.W * X'A * FA) := by
    have h := s.φ ΦA hΦA
    rw [Matrix.map_mul] at h
    have e1 : (s.X'.map bk.iS).map ΦA = φX'A := by
      rw [Matrix.map_map, hφX'A]; congr 1; funext x; exact hΦiS x
    rw [e1] at h
    simpa only [map_natCast, map_pow] using h
  have hXXφ : φX'A * φXA = (L ^ s.c₂ * φe ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    have h := congrArg (fun M => M.map (bk.iS.comp (frobS l bk.a))) hXX
    simp only [Matrix.map_mul, map_smul_ringHom, Matrix.map_one _ (map_zero _) (map_one _), map_mul, map_pow,
      map_natCast] at h
    exact h
  have hXX2 : XA * X'A = (L ^ s.c₂ * e ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    have h := congrArg (fun M => M.map bk.iS) s.X_mul
    simp only [Matrix.map_mul, map_smul_ringHom, Matrix.map_one _ (map_zero _) (map_one _), map_mul, map_pow,
      map_natCast] at h
    exact h
  have hQ : (L ^ s.c₁ * L ^ s.c₂ * φe ^ s.N) • s.W.map ΦA = s.W * X'A * FA * φXA := by
    apply ((hφE.pow s.N).smul_left_cancel).1
    calc φe ^ s.N • (L ^ s.c₁ * L ^ s.c₂ * φe ^ s.N) • s.W.map ΦA
        = (L ^ s.c₁ • (s.W.map ΦA * φX'A)) * φXA := by
          rw [Matrix.smul_mul, Matrix.mul_assoc, hXXφ, Matrix.mul_smul, Matrix.mul_one, smul_smul, smul_smul]
          congr 1; ring
      _ = _ := by rw [hS, Matrix.smul_mul]
  have hD : s.W * ((L ^ s.c₁ * L ^ s.c₂ * φe ^ s.N) • (Zi * AA) - e ^ ht.a • (X'A * FA * φXA * ZΦ)) = 0 := by
    rw [Matrix.mul_sub, sub_eq_zero, Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc, hW, ← hP, ← hWΦ,
      smul_comm, ← Matrix.smul_mul, hQ]
    simp only [Matrix.mul_assoc]
  have hD' := eq_zero_of_mul_eq_zero_of_mul_eq_smul (pow_mem hτr _) s.W_mul hD
  rw [sub_eq_zero] at hD'
  have hX := congrArg (fun M => XA * M) hD'
  simp only [Matrix.mul_smul, ← Matrix.mul_assoc, hXX2, Matrix.smul_mul, Matrix.one_mul, smul_smul] at hX
  have G : (L ^ s.c₁ * φe ^ s.N) • (XA * Zi * AA) = e ^ (ht.a + 2 * s.N) • (FA * (φXA * ZΦ)) := by
    apply ((hL.pow s.c₂).smul_left_cancel).1
    rw [smul_smul, smul_smul]
    calc (L ^ s.c₂ * (L ^ s.c₁ * φe ^ s.N)) • (XA * Zi * AA) = (L ^ s.c₁ * L ^ s.c₂ * φe ^ s.N) • (XA * Zi * AA) := by
          congr 1; ring
      _ = _ := by rw [hX, ← Matrix.mul_assoc]; congr 1; ring
  exact G

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCountDirectLiftingProof
section
noncomputable section

namespace GlobalTheory.Pass.LocDirect

open _root_.Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem main : StepLocDirect := by
  intro D hLOC hBK hFont hPDR i r hr Xs w hw hdeg n e hPot hLift k M hSub
  have hM : Continuous fun g => M g := hSub.1
  have hc : ∀ x, Continuous fun g => Br.loc D.nbr i w hw (rTwO D.nd i r x) g := fun x =>
    GlobalTheory.PotDual.continuous_loc D i w hw _ (FamCont.stepCont D i r hr x).1
  unfold LocBoundP
  have hcut : cutCoc i w hw r Xs M = ⋃₀ {A | ∃ (a : ℕ) (x : Fin a → D.nd.X i) (_ : ∀ j, x j ∈ Xs)
      (E : Fin a → Fin D.R.nV → KK D.nd i) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) (_ : Y.FG)
      (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)
      (hE : ∀ γ : GE D.nd, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (E j) - E j) ∈ Y),
      A = LocDirect.pushSet i w hw r M x E Y hst hE} := by
    ext c
    rw [LocDirect.mem_cutCoc, Set.mem_sUnion]
    constructor
    · rintro ⟨a, x, hx, E, Y, hY, hst, hE, hc⟩
      exact ⟨_, ⟨a, x, hx, E, Y, hY, hst, hE, rfl⟩, hc⟩
    · rintro ⟨_, ⟨a, x, hx, E, Y, hY, hst, hE, rfl⟩, hc⟩
      exact ⟨a, x, hx, E, Y, hY, hst, hE, hc⟩
  rw [hcut]
  apply _root_.GlobalTheory.Pass.LocDirect.lenMod_span_sUnion_le_of_directed
  · rintro _ ⟨a₁, x₁, hx₁, E₁, Y₁, hY₁, hst₁, hE₁, rfl⟩ _ ⟨a₂, x₂, hx₂, E₂, Y₂, hY₂, hst₂, hE₂, rfl⟩
    obtain ⟨a, x, hx, E, Y, hY, hst, hE, h1, h2⟩ :=
      _root_.GlobalTheory.Pass.LocDirect.pushSet_merge D i w hw r Xs M a₁ x₁ hx₁ E₁ Y₁ hY₁ hst₁ hE₁ a₂ x₂ hx₂ E₂ Y₂ hY₂ hst₂ hE₂
    exact ⟨_, ⟨a, x, hx, E, Y, hY, hst, hE, rfl⟩, h1, h2⟩
  · rintro _ ⟨a, x, hx, E, Y, hY, hst, hE, rfl⟩
    let U := LocDirect.ModuleGaloisRepresentation i w hw M hM
    let X := LocDirect.Xgrep i w hw r x (fun j => hc (x j)) Y hst
    obtain ⟨K', hK', hcrys⟩ := GlobalTheory.T.tensorLocalField_isCrystalline_over_familyField D hFont i r hr Xs w hw n hPot M hSub hM
    have hUdR : IsDR (Br.PD D.loc D.nbr i w hw) U.ρ :=
      hPDR (D.nd.l i) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL hK' U hcrys
    obtain ⟨U', LT', PU, hdual, hrank⟩ := GlobalTheory.T.crystalline_over_extension D hFont hBK hPDR i w hw hdeg M hM K' hK' hcrys
    obtain ⟨X', PX, hX⟩ := _root_.GlobalTheory.TateDualX.exists_tateDual D i w hw X
    have hLA := _root_.GlobalTheory.Pass.LocDirect.liftAll_of_liftFamW D i w hw r hr Xs e hLift M hSub hM a x hx (fun j => hc (x j)) Y hst
    have hsub := GlobalTheory.T.pushouts_mem_span_localSelmerPushouts D hFont i r hr Xs w hw n hPot M hM a x hx (fun j => hc (x j)) E Y hY hst hE
    obtain ⟨m, k', hm, hk', hle⟩ := hLOC.2 (D.nd.l i) (D.nbr i w hw).Kw (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)
      (goodO_ringOfIntegers _ _) X X U X' U' 1 PX PU (Br.locLat D.nbr i w hw M) LT' e
      ⟨⟨LinearEquiv.refl _ _, fun g v => by simp⟩, hUdR, hX, hdual, Or.inl hLA⟩
    have hmono := _root_.GlobalTheory.lenMod_mono_left _ _ (HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M))
      (Submodule.span_le.2 hsub)
    have hT : finrank (Br.OLL D.nbr i w hw) ↥(Br.locLat D.nbr i w hw M).T = k := by
      have hinj := stdG_inj (O := Br.OLL D.nbr i w hw) (LL := Br.LL D.nbr i w hw) Subtype.val_injective k
      show finrank _ ↥(stdG (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) k) = k
      exact (LinearEquiv.ofInjective _ hinj).finrank_eq.symm.trans (Module.finrank_fin_fun _)
    have h2 : m ≤ 2 * k * e * k' := by
      refine hle.trans ?_
      calc _ ≤ e * (k + k) * k' := by
            gcongr
            · exact hrank
            · exact hT.le
        _ = 2 * k * e * k' := by ring
    calc _ ≤ BlochKatoDuality.lenMod (BlochKatoDuality.spanPush (Br.PD D.loc D.nbr i w hw) X U (Br.locLat D.nbr i w hw M))
          (HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M)) := hmono
      _ = (m : ℕ∞) := hm
      _ ≤ ((2 * k * e * k' : ℕ) : ℕ∞) := by exact_mod_cast h2
      _ = _ := by
        rw [show lenOl (Br.PD D.loc D.nbr i w hw) (O := Br.OLL D.nbr i w hw) = (k' : ℕ∞) from hk']
        push_cast; ring

end GlobalTheory.Pass.LocDirect
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalUpperUnipotentAdelicUpperUnipotent
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspRep

theorem cornerGL_apply_loctri {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) (i j : Fin a) :
    (cornerGL a s g).val i j = (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s (g.val i j) :=
  rfl

theorem cornerGL_apply_ne_loctri {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) {i j : Fin a} (h : i ≠ j) :
    (cornerGL a s g).val i j = s (g.val i j) := by
  rw [cornerGL_apply_loctri]
  simp [Matrix.one_apply_ne h]

theorem cornerGL_apply_diag_loctri {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) {j : Fin a} (h : g.val j j = 1) :
    (cornerGL a s g).val j j = 1 := by
  rw [cornerGL_apply_loctri, h]
  simp

theorem locTri_adelic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (u : GL (Fin a) (w.adicCompletion E)), (∀ i j : Fin a, j < i → u.val i j = 0) → (∀ j : Fin a, u.val j j = 1) → (∀ i j : Fin a, j < i → (finGL E a (locGL E a w u)).val i j = 0) ∧ (∀ j : Fin a, (finGL E a (locGL E a w u)).val j j = 1) ∧ ∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, (finGL E a (locGL E a w u)).val p.1 p.2 = sFin E (sLoc E w (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2)) := by
  intro E _ _ _ a w u hlow hdiag
  have hoff : ∀ i j : Fin a, i ≠ j → (finGL E a (locGL E a w u)).val i j = sFin E (sLoc E w (u.val i j)) := by
    intro i j h
    rw [finGL, cornerGL_apply_ne_loctri _ _ h, locGL, cornerGL_apply_ne_loctri _ _ h]
  refine ⟨?_, ?_, ?_⟩
  · intro i j h
    rw [hoff i j (ne_of_gt h), hlow i j h, map_zero, map_zero]
  · intro j
    exact cornerGL_apply_diag_loctri _ _ (cornerGL_apply_diag_loctri _ _ (hdiag j))
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' : (p.2 : ℕ) = p.1 + 1 := (Finset.mem_filter.mp hp).2
      have hne : p.1 ≠ p.2 := by
        intro h; rw [h] at hp'; omega
      exact hoff p.1 p.2 hne

end GlobalTheory.CuspRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyImageMemBdRplusLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
open GlobalTheory.GalStep in
theorem GlobalTheory.GalStep.taylor_rho : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → ∀ (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T), (∀ (c : ι → OA l ↥(OL LL)) (z : TW (OA l ↥(OL LL)) T), I.j (inclV l ↥(OL LL) ι c) = TWincl (inclO l ↥(OL LL)) T z → jD (fun i => toOD l ↥(OL LL) (c i)) = TWincl (toOD l ↥(OL LL)) T z) → ∀ α : ℕ, (∀ v ∈ P.L, E ↥LL.1 l e ^ α • v ∈ P.M) → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∃ v : OD l ↥(OL LL), IsUnit v ∧ ∀ w ∈ P.Mext (invL l (S ↥(OL LL) ↥LL.1 e)), ∀ (R : ℕ) (j : ι), GlobalTheory.GalStep.rhoD T jD g (GlobalTheory.GalStep.YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xiExt w)) j - v ^ α * ∑ i ∈ Finset.range R, toOD l ↥(OL LL) (1 ⊗ₜ ϖ.mu (sQ l g)) ^ i * Ring.inverse (i.factorial : OD l ↥(OL LL)) * GlobalTheory.GalStep.YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xiExt (fun τ k => descN ↥LL.1 i (w τ k))) j ∈ Ideal.span {GlobalTheory.GalStep.ED ↥LL.1 (thetaW a LL) ϖ ^ R} := by
  intro hF l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I jB Pl AI hStd hCmp hHor jD hjD α hα g hg
  obtain ⟨v, hv, hED⟩ := _root_.GlobalTheory.GalStep.galOD_ED l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ (sQ l g) hg
  refine ⟨v, hv, fun w hw R j => ?_⟩
  exact taylor_vec (thetaW a LL) ϖ P α (descN_mem_Mext P) (E_pow_xiExt_mem_Man P α hα)
    (galOD ↥(OL LL) (sQ l g)) (rhoDHom T jD g) (rhoD_smul T jD g) (v ^ α)
    (GlobalTheory.T.breuilKisin_galois_scales_deRhamPeriods_by_unit_pow hF l a e ϖ LL hl2 ι P T I jB Pl AI hStd hCmp hHor jD hjD α hα g hg v hED)
    (fun i => toOD l ↥(OL LL) (1 ⊗ₜ ϖ.mu (sQ l g)) ^ i * Ring.inverse (i.factorial : OD l ↥(OL LL))) R _
    (fun f hf => _root_.GlobalTheory.GalStep.taylor_iD_mod_ED l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ (sQ l g) hg f hf R) hw j


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
open GlobalTheory.GalStep in
theorem GlobalTheory.GalStep.key_sums (hF : GlobalTheory.Published.FontaineBcris) (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (hl2 : l ≠ 2) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (hStd : IsStd Pl AI) (hCmp : IsCrisCmp I jB) (hHor : IsHoriz (thetaW a LL) ϖ (sQ l) P jB) (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T) (hjD : ∀ (c : ι → OA l ↥(OL LL)) (z : TW (OA l ↥(OL LL)) T), I.j (inclV l ↥(OL LL) ι c) = TWincl (inclO l ↥(OL LL)) T z → jD (fun i => toOD l ↥(OL LL) (c i)) = TWincl (toOD l ↥(OL LL)) T z)
    (α b : ℕ) (hα : ∀ v ∈ P.L, E ↥LL.1 l e ^ α • v ∈ P.M) (g : Gl l) (hg : sQ l g ∈ GK (ϖ.field a)) (ε : OCb l) (c : ℕ)
    (hk : ∀ k : ℕ, ϖ.kummer (sQ l (g ^ k)) = ε ^ (c * k)) {m : Vec ↥LL.1 a ι} (hm : m ∈ P.M)
    {wx : Vec ↥LL.1 a ι} (hwx : wx ∈ P.Mext (invL l (S ↥(OL LL) ↥LL.1 e))) (hwxdef : P.xiExt wx = E ↥LL.1 l e ^ b • m) (j : ι)
    (k : ℕ) : ∑ i ∈ Finset.range (α + b), ((toOD l ↥(OL LL) (1 ⊗ₜ WittVector.teichmuller l ε) ^ c) ^ k - 1) ^ i *
      Ring.inverse (i.factorial : OD l ↥(OL LL)) *
      YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xiExt (fun τ k => descN ↥LL.1 i (wx τ k))) j ∈
      Ideal.span {ED ↥LL.1 (thetaW a LL) ϖ ^ (α + b)} := by
  have hgk : sQ l (g ^ k) ∈ GK (ϖ.field a) := by rw [map_pow]; exact Subgroup.pow_mem _ hg k
  obtain ⟨v, hv, htay⟩ := taylor_rho hF l a e ϖ LL hl2 ι P T I jB Pl AI hStd hCmp hHor jD hjD α hα (g ^ k) hgk
  have h1 := htay wx hwx (α + b) j
  obtain ⟨v', hv', hED⟩ := _root_.GlobalTheory.GalStep.galOD_ED l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ (sQ l (g ^ k)) hgk
  have hxe : E ↥LL.1 l e ^ α • P.xiExt wx = E ↥LL.1 l e ^ (α + b) • m := by
    rw [hwxdef, smul_smul, ← pow_add]
  have h2 : rhoD T jD (g ^ k) (YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xiExt wx)) j ∈
      Ideal.span {ED ↥LL.1 (thetaW a LL) ϖ ^ (α + b)} := by
    rw [hxe, YD_E_pow_smul (thetaW a LL) ϖ (P.M_le_Man hm) (α + b), rhoD_smul, Pi.smul_apply, smul_eq_mul, map_pow,
      hED, mul_pow, mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have h3 : toOD l ↥(OL LL) (1 ⊗ₜ ϖ.mu (sQ l (g ^ k))) = (toOD l ↥(OL LL) (1 ⊗ₜ WittVector.teichmuller l ε) ^ c) ^ k - 1 := by
    rw [PiSys.mu, hk k, TensorProduct.tmul_sub, map_sub, ← Algebra.TensorProduct.one_def, map_one,
      ← pow_mul, ← map_pow, Algebra.TensorProduct.tmul_pow, one_pow, map_pow (WittVector.teichmuller l)]
  rw [h3] at h1
  have h4 := sub_mem h2 h1
  rw [sub_sub_cancel] at h4
  have h5 := Ideal.mul_mem_left _ (↑(hv.pow α).unit⁻¹ : OD l ↥(OL LL)) h4
  rwa [← mul_assoc, IsUnit.val_inv_mul, one_mul] at h5


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
open GlobalTheory.GalStep in
theorem GlobalTheory.GalStep.main : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → ∀ (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T), (∀ (c : ι → OA l ↥(OL LL)) (z : TW (OA l ↥(OL LL)) T), I.j (inclV l ↥(OL LL) ι c) = TWincl (inclO l ↥(OL LL)) T z → jD (fun i => toOD l ↥(OL LL) (c i)) = TWincl (toOD l ↥(OL LL)) T z) → ∀ m ∈ P.M, ∀ n : ℕ, E ↥LL.1 l e ^ n • P.EN m ∈ P.Man → ∀ w : ZMod a → ι → Ahat ↥(OL LL) ↥LL.1 l e, (∀ τ i, algebraMap _ (AhatE ↥(OL LL) ↥LL.1 l e) (w τ i) = hat ↥(OL LL) l e ((E ↥LL.1 l e ^ n • P.EN m) τ i)) → ∀ i, ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => w τ i) ∈ Ideal.span {ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) ^ n} := by
  intro hF l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I jB Pl AI hStd hCmp hHor jD hjD m hm n hn w hw j
  obtain ⟨α, β₀, hα, hβ₀⟩ := P.exists_exponents
  have hβ : E ↥LL.1 l e ^ (β₀ + n) • m ∈ P.L := by
    have h1 := P.L.smul_mem (⟨E ↥LL.1 l e ^ n, pow_mem (E_mem l e _) n⟩ : A ↥(OL LL) ↥LL.1) (hβ₀ m hm)
    have h2 : E ↥LL.1 l e ^ (β₀ + n) • m =
        (⟨E ↥LL.1 l e ^ n, pow_mem (E_mem l e _) n⟩ : A ↥(OL LL) ↥LL.1) • E ↥LL.1 l e ^ β₀ • m := by
      rw [pow_add, mul_comm, mul_smul]
      rfl
    rw [h2]
    exact h1
  obtain ⟨g, ε, c, hε, hc, hg, hk⟩ := _root_.GlobalTheory.KummerMove.main l a e ϖ hl2
  obtain ⟨u, hu, hq⟩ := _root_.GlobalTheory.GalStep.teich_pow_sub_one_eq_ED_mul l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ε c hε hc
  obtain ⟨hnz, hnat⟩ := _root_.GlobalTheory.GalStep.ED_nzd_and_natCast_isUnit l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ
  have hxM : E ↥LL.1 l e ^ (β₀ + n) • m ∈ P.MMl := P.ext_mono (le_trans (A_le_S l e) (le_away _ _)) hβ
  have hsurj := P.xiExt.surjective (E ↥LL.1 l e ^ (β₀ + n) • m)
  obtain ⟨wx, hwxdef⟩ := hsurj
  have hwx : wx ∈ P.Mext (invL l (S ↥(OL LL) ↥LL.1 e)) :=
    ((GlobalTheory.BK.xi_trivialises_invL_S ↥(OL LL) ↥LL.1 l e a ι P).2 wx).1 (by rw [hwxdef]; exact hxM)
  have hD1 := _root_.GlobalTheory.FilCoeff.d_mul_x_one_mem_span_pow (OD l ↥(OL LL)) hnat (ED ↥LL.1 (thetaW a LL) ϖ) _ u hu hq (α + (β₀ + n))
    (fun i => YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xiExt (fun τ k => descN ↥LL.1 i (wx τ k))) j)
    (key_sums hF l a e ϖ LL hl2 ι P T I jB Pl AI hStd hCmp hHor jD hjD α (β₀ + n) hα g hg ε c hk hm hwx hwxdef j)
  have hfin := tail_step (thetaW a LL) ϖ P hnz (E_pow_xiExt_mem_Man P) (descN_mem_Mext P) α β₀ n hα hm hn hwx hwxdef j hD1
  rw [← iD_eq_YD (thetaW a LL) ϖ hn j (fun τ => w τ j) (fun τ => hw τ j)] at hfin
  exact hfin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultisetProdMapProductEqProdProd
section
noncomputable section

namespace GlobalTheory.JSW

open Finset

theorem cauchy_local {m n : ℕ} (hmn : m ≤ n) (α : Fin n → ℂ) (β : Fin m → ℂ) (T : ℂ)
    (hs : Summable fun l : {l : Fin m → ℕ // Antitone l} =>
      ‖schurAt (padTo hmn l.1) α * schurAt l.1 β‖ * ‖T‖ ^ (∑ i, l.1 i)) :
    (∀ i j, 1 - α i * β j * T ≠ 0) ∧
    HasSum (fun l : {l : Fin m → ℕ // Antitone l} =>
      schurAt (padTo hmn l.1) α * schurAt l.1 β * T ^ (∑ i, l.1 i))
      (∏ i, ∏ j, (1 - α i * β j * T)⁻¹) := by
  set G : (Fin m → ℕ) → ℂ := fun l => schurAt (padTo hmn l) α * schurAt l β * T ^ (∑ i, l i) with hGdef
  have hG : Summable fun l : {l : Fin m → ℕ // Antitone l} => ‖G l.1‖ := by
    refine hs.congr fun l => ?_
    simp [G, norm_pow]
  obtain ⟨hsum, htrans⟩ := GlobalTheory.T.hasSum_regroup_antitonePartitions_by_degree G hG
  have hc : (fun d => ∑ l ∈ antiParts m d, G l) = fun d => T ^ d * ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
      ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j) := by
    funext d
    rw [← _root_.GlobalTheory.JSW.CauchyGlue.cauchy_formal hmn α β d, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    simp only [G]; rw [(mem_antiParts.1 hl).1]; ring
  have h5 := _root_.GlobalTheory.JSW.mk_sum_prod_hsymm_mul_prod_one_sub α β T
  rw [← hc] at h5
  obtain ⟨hne, hhas⟩ := GlobalTheory.T.eulerInverse_powerSeries_eval_one _ hsum (fun p : Fin n × Fin m => α p.1 * β p.2 * T) h5
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Fintype.prod_prod_type] at hne
    exact Finset.prod_ne_zero_iff.1 (Finset.prod_ne_zero_iff.1 hne i (mem_univ _)) j (mem_univ _)
  · have := htrans _ hhas
    rw [← Finset.prod_inv_distrib, Fintype.prod_prod_type] at this
    exact this

theorem multiset_prod_map_product_eq_prod_prod {X Y : Type} (A : Multiset X) (B : Multiset Y) (f : X × Y → ℂ) :
    ((A ×ˢ B).map f).prod = (A.map fun a => (B.map fun b => f (a, b)).prod).prod := by
  induction A using Multiset.induction_on with
  | empty => simp
  | cons a A ih => simp [Multiset.cons_product, ih]

theorem locL_univ (q : ℕ) {m n : ℕ} (α : Fin n → ℂˣ) (β : Fin m → ℂˣ) (s : ℂ) :
    locL q (Finset.univ.val.map α) (Finset.univ.val.map β) s =
      ∏ i, ∏ j, (1 - (α i : ℂ) * β j * (q : ℂ) ^ (-s))⁻¹ := by
  rw [locL, multiset_prod_map_product_eq_prod_prod, Multiset.map_map]
  simp only [Multiset.map_map, Function.comp_def]
  rfl

theorem cauchy_locL {m n : ℕ} (hmn : m ≤ n) (α : Fin n → ℂˣ) (β : Fin m → ℂˣ) (q : ℕ) (s : ℂ)
    (hs : Summable fun l : {l : Fin m → ℕ // Antitone l} =>
      ‖schurAt (padTo hmn l.1) (fun i => (α i : ℂ)) * schurAt l.1 (fun j => (β j : ℂ))‖ *
        ‖(q : ℂ) ^ (-s)‖ ^ (∑ i, l.1 i)) :
    HasSum (fun l : {l : Fin m → ℕ // Antitone l} => schurAt (padTo hmn l.1) (fun i => (α i : ℂ)) *
      schurAt l.1 (fun j => (β j : ℂ)) * ((q : ℂ) ^ (-s)) ^ (∑ i, l.1 i))
      (locL q (Finset.univ.val.map α) (Finset.univ.val.map β) s) := by
  rw [locL_univ]; exact (cauchy_local hmn _ _ _ hs).2

end GlobalTheory.JSW
end
end

