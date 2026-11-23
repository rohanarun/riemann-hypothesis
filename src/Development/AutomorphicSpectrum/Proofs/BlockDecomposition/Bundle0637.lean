module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0044
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0045
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0624
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0628
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitNDgOfLocalOfSteps
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHtHalfSub
section
noncomputable section

open NumberField Matrix
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.So GroundTheory.Global

namespace GlobalTheory.CompanionTheory.EisJMir

section Gen

variable {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']

theorem isHt_pull (j : G →* G') (hj : Continuous j) {Γ K P : Subgroup G} {Γ' K' P' : Subgroup G'} {η : G' → ℝ}
    (h : IsHt Γ' K' P' η) (hΓ : ∀ γ ∈ Γ, j γ ∈ Γ') (hK : ∀ k ∈ K, j k ∈ K') (hP : ∀ p ∈ P, j p ∈ P') :
    IsHt Γ K P (fun x => η (j x)) := by
  refine ⟨fun p hp g => ?_, fun g k hk => ?_, fun γ hγ hγP => ?_, h.cont.comp hj⟩
  · rw [map_mul]
    exact h.left (j p) (hP p hp) (j g)
  · rw [map_mul]
    exact h.right (j g) (j k) (hK k hk)
  · exact h.rat (j γ) (hΓ γ hγ) (hP γ hγP)

theorem isHt_of_top {Γ K P : Subgroup G} {η : G → ℝ} (h : IsHt Γ K ⊤ η) : IsHt Γ K P η := by
  exact ⟨fun p _ g => h.left p (Subgroup.mem_top p) g, h.right, fun γ hγ _ => h.rat γ hγ (Subgroup.mem_top γ),
    h.cont⟩

theorem isHt_half_add {Γ K P : Subgroup G} {a b : G → ℝ} (ha : IsHt Γ K P a) (hb : IsHt Γ K P b) :
    IsHt Γ K P (fun x => (a x + b x) / 2) := by
  refine ⟨fun p hp g => ?_, fun g k hk => ?_, fun γ hγ hγP => ?_, (ha.cont.add hb.cont).div_const 2⟩
  · rw [ha.left p hp g, hb.left p hp g]
    ring
  · rw [ha.right g k hk, hb.right g k hk]
  · rw [ha.rat γ hγ hγP, hb.rat γ hγ hγP]
    norm_num

theorem isHt_half_sub {Γ K P : Subgroup G} {a b : G → ℝ} (ha : IsHt Γ K P a) (hb : IsHt Γ K P b) :
    IsHt Γ K P (fun x => (a x - b x) / 2) := by
  refine ⟨fun p hp g => ?_, fun g k hk => ?_, fun γ hγ hγP => ?_, (ha.cont.sub hb.cont).div_const 2⟩
  · rw [ha.left p hp g, hb.left p hp g]
    ring
  · rw [ha.right g k hk, hb.right g k hk]
  · rw [ha.rat γ hγ hγP, hb.rat γ hγ hγP]
    norm_num

theorem isCh_pull (j : G →* G') (hj : Continuous j) {Γ P : Subgroup G} {Γ' P' : Subgroup G'} {u : G' → ℂ} {c : G → ℂ}
    (hu : IsCh Γ' P' u) (hc : IsCh Γ ⊤ c) (hΓ : ∀ γ ∈ Γ, j γ ∈ Γ') (hP : ∀ p ∈ P, j p ∈ P') :
    IsCh Γ P (fun x => u (j x) * (c x)⁻¹) := by
  have hc0 : ∀ x, c x ≠ 0 := fun x h0 => by
    have h1 := hc.norm x (Subgroup.mem_top x)
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  refine ⟨fun p hp q hq => ?_, fun p hp => ?_, fun γ hγ hγP => ?_, ?_⟩
  · rw [map_mul, hu.mul (j p) (hP p hp) (j q) (hP q hq), hc.mul p (Subgroup.mem_top p) q (Subgroup.mem_top q),
      mul_inv]
    ring
  · rw [norm_mul, norm_inv, hu.norm (j p) (hP p hp), hc.norm p (Subgroup.mem_top p)]
    norm_num
  · rw [hu.rat (j γ) (hΓ γ hγ) (hP γ hγP), hc.rat γ hγ (Subgroup.mem_top γ)]
    norm_num
  · refine (hu.cont.comp hj.continuousOn (fun x hx => hP x hx)).mul ?_
    exact (hc.cont.mono (fun x _ => Subgroup.mem_top x)).inv₀ (fun x _ => hc0 x)

end Gen

theorem jmir : StdGood → GrpTop → BdetLaw → ExtLaw → ParLaw → JTop → JCpt → JPar → JIwa → JRat → JCh → JMir := by
  intro hStd hGT hBd hExt hPar hJT hJC hJP hJI hJR hJCh F E R _ _ _ _ _ _ _ _ _ _ A ε ν r δ α ω ι _ _ i j hA hB
    hi hJ hIwa
  obtain ⟨hjc, -, -, -⟩ := hJT F E R A ε ν r δ α ω ι i j hA hB hi hJ
  have hcK := hJC F E R A ε ν r δ α ω ι i j hA hB hi hJ
  obtain ⟨hst, hQeq, hbd⟩ := hJP F E R A ε ν r δ α ω ι i j hA hB hi hJ
  have hIw := hJI F E R A ε ν r δ α ω ι i j hA hB hi hJ
  obtain ⟨hmapΓ, htr⟩ := hJR F E R A ε ν r δ α ω ι i j hA hB hi hJ
  obtain ⟨hc0, hld⟩ := hJCh F E R A ε ν r δ α ω ι i j hA hB hi hJ
  obtain ⟨hparU, hhtU, -⟩ := (hPar E R A hA ι ε Set.univ).2 (by rw [inf_idem]; exact hIwa)
  rw [inf_idem] at hparU
  have hGL := hA.toGoodL
  have hSG := (hStd F).lgmul
  have hlg1 : A.lg 1 = 0 := by
    have h := hGL.lgmul 1 1
    rw [mul_one] at h
    linarith
  have hP : ∀ p ∈ Subgroup.comap (prj A ν ι) (stab 𝔸[𝓞 F, F] {(Sum.inl i : ι ⊕ ι)}),
      j p ∈ A.uQ ε Set.univ := by
    intro p hp
    rw [← hQeq] at hp
    exact hp
  have hK : ∀ k ∈ cK α j, j k ∈ A.uK ε ι := fun k hk => (Subgroup.mem_inf.1 hk).1
  have hΓ : ∀ γ ∈ cΓ A ν ι, j γ ∈ A.uΓ ε ι := by
    intro γ hγ
    rw [← hmapΓ]
    exact Subgroup.mem_map_of_mem j hγ
  have hωsq : ∀ y : IdeleGroup F, ω.toIdele y * ω.toIdele y = 1 := by
    intro y
    rw [hB.ωχ, mul_eq_one_iff_eq_inv]
    have h1 := hA.χσ (Units.map (ν : 𝔸[𝓞 F, F] →* R) y)
    convert h1 using 2
    all_goals (ext; simp [hB.fix])
  have hcov : ∀ x : cover A ν ι, A.lg (x : Rˣ × GL (ι ⊕ ι) 𝔸[𝓞 F, F]).1 =
      -(adStd F).lg (Matrix.GeneralLinearGroup.det (prj A ν ι x)) ∧
      A.χ (Units.map (ν : 𝔸[𝓞 F, F] →* R) (Matrix.GeneralLinearGroup.det (prj A ν ι x))) = 1 := by
    intro x
    have hx := MonoidHom.mem_ker.1 x.2
    simp only [MonoidHom.mul_apply, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst,
      MonoidHom.coe_snd] at hx
    constructor
    · have h := congrArg A.lg hx
      rw [hGL.lgmul, hGL.lgmul, hB.lgσ, hB.lg, hlg1] at h
      show A.lg (x : Rˣ × GL (ι ⊕ ι) 𝔸[𝓞 F, F]).1 = -(adStd F).lg (Matrix.GeneralLinearGroup.det (x : Rˣ × GL (ι ⊕ ι) 𝔸[𝓞 F, F]).2)
      linarith
    · have h := congrArg A.χ hx
      rw [map_mul, map_mul, hA.χσ, map_one, mul_inv_cancel, one_mul] at h
      exact h
  have hext : ∀ x ∈ Subgroup.comap (prj A ν ι) (stab 𝔸[𝓞 F, F] {(Sum.inl i : ι ⊕ ι)}),
      A.uH ε Set.univ (j x) = A.lg (bdet (Sum.inl '' (Set.univ : Set ι)) ((j x : A.U ε ι) : GL (ι ⊕ ι) R)) := by
    intro x hx
    obtain ⟨-, -, -, hT2U, -, -, hKc⟩ := hGT E R A hA ι ε
    haveI := hT2U
    obtain ⟨-, hmulS, hcontS, hratS, hkS, -⟩ := hBd E R A hGL (ι ⊕ ι) (Sum.inl '' (Set.univ : Set ι))
    have h := (hExt (A.U ε ι) (A.uΓ ε ι) (A.uK ε ι) (A.uQ ε Set.univ)
      (fun p => A.lg (bdet (Sum.inl '' (Set.univ : Set ι)) (p : GL (ι ⊕ ι) R))) hKc hparU.closed hIwa
      (fun p hp q hq => by
        show A.lg (bdet _ ((p * q : A.U ε ι) : GL (ι ⊕ ι) R)) = _
        rw [Subgroup.coe_mul, hmulS _ (Subgroup.mem_subgroupOf.1 hp) _ (Subgroup.mem_subgroupOf.1 hq), hGL.lgmul])
      (hGL.lgcont.comp_continuousOn (hcontS.comp continuous_subtype_val.continuousOn
        (fun p hp => Subgroup.mem_subgroupOf.1 hp)))
      (fun p hp hk => hkS _ (Subgroup.mem_subgroupOf.1 hp) (Subgroup.mem_subgroupOf.1 hk))
      (fun p hp hg => by
        obtain ⟨e, he⟩ := hratS _ (Subgroup.mem_subgroupOf.1 hp) (Subgroup.mem_subgroupOf.1 hg)
        show A.lg _ = 0
        rw [he]
        exact hGL.lgi e)).2 (j x) (hP x hx) 1 (Subgroup.one_mem _)
    rw [mul_one] at h
    exact h
  refine ⟨?_, ?_, ?_, hcK, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hld, ?_, ?_, fun g => rfl⟩
  · have h1 : 0 < Fintype.card ι := Fintype.card_pos_iff.2 ⟨i⟩
    rw [Fintype.card_sum]
    omega
  · refine ContinuousMonoidHom.ext fun x => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    exact hωsq y
  · exact continuous_snd.comp continuous_subtype_val
  · intro κ hκ
    obtain ⟨κ', hκ', hEq⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hκ).2)
    refine ⟨κ', hκ', ?_⟩
    have hd : (fun k : ι ⊕ ι => ((Sum.elim (fun _ => (1 : IdeleGroup F)) (fun _ => α) k : IdeleGroup F) : 𝔸[𝓞 F, F])) =
        (Sum.elim (fun _ => 1) (fun _ => (α : 𝔸[𝓞 F, F])) : ι ⊕ ι → 𝔸[𝓞 F, F]) := by
      funext k
      rcases k with k | k <;> rfl
    rw [hd]
    change ((prj A ν ι κ : GL (ι ⊕ ι) 𝔸[𝓞 F, F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[𝓞 F, F]) * ((dg ι α : GL (ι ⊕ ι) 𝔸[𝓞 F, F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[𝓞 F, F]) =
      ((dg ι α : GL (ι ⊕ ι) 𝔸[𝓞 F, F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[𝓞 F, F]) * (κ' : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[𝓞 F, F])
    rw [← hEq]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← Units.val_mul, inv_mul_cancel_right, Units.val_mul]
  · intro γ hγ
    exact (Subgroup.mem_prod.1 (Subgroup.mem_subgroupOf.1 hγ)).2
  · intro s hs g hg
    obtain ⟨γ, hγ, h⟩ := htr g hg
    refine ⟨γ, hγ, ?_⟩
    rcases hs with rfl | rfl
    · exact h
    · rw [hst]
      exact h
  · refine ⟨?_, hIw, isCh_pull j hjc hparU.ch hc0 hΓ hP⟩
    rw [← hQeq, Subgroup.coe_comap]
    exact hparU.closed.preimage hjc
  · rw [hst]
    refine ⟨?_, hIw, isCh_pull j hjc hparU.ch hc0 hΓ hP⟩
    rw [← hQeq, Subgroup.coe_comap]
    exact hparU.closed.preimage hjc
  · exact isHt_half_add (isHt_pull j hjc hhtU hΓ hK hP) (isHt_of_top hld)
  · rw [hst]
    exact isHt_half_sub (isHt_pull j hjc hhtU hΓ hK hP) (isHt_of_top hld)
  · intro p hp
    obtain ⟨hb1, -⟩ := hbd p hp
    obtain ⟨hl, -⟩ := hcov p
    refine ⟨?_, ?_⟩
    · show (A.χ (bdet (Sum.inl '' Set.univ) ((j p : A.U ε ι) : GL (ι ⊕ ι) R)) : ℂ) *
          ((A.χ (p : Rˣ × GL (ι ⊕ ι) 𝔸[𝓞 F, F]).1 : ℂ))⁻¹ = _
      rw [hb1, map_mul, Circle.coe_mul, hB.ωχ, mul_comm, ← mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero _),
        one_mul]
    · show (A.uH ε Set.univ (j p) + ld p) / 2 = _
      rw [hext p hp, hb1, hGL.lgmul, hB.lg, hl]
      simp only [So.ld]
      ring
  · intro p hp
    rw [hst] at hp
    obtain ⟨hb1, hb2⟩ := hbd p hp
    obtain ⟨hl, hχ⟩ := hcov p
    have hωb : ω.toIdele (bdet {Sum.inl i} (prj A ν ι p)) = ω.toIdele (bdet {Sum.inr i} (prj A ν ι p)) := by
      have h3 : ω.toIdele (bdet {Sum.inl i} (prj A ν ι p)) * ω.toIdele (bdet {Sum.inr i} (prj A ν ι p)) = 1 := by
        rw [hB.ωχ, hB.ωχ, ← map_mul, ← map_mul, ← hb2]
        exact hχ
      exact mul_right_cancel (h3.trans (hωsq _).symm)
    refine ⟨?_, ?_⟩
    · show (A.χ (bdet (Sum.inl '' Set.univ) ((j p : A.U ε ι) : GL (ι ⊕ ι) R)) : ℂ) *
          ((A.χ (p : Rˣ × GL (ι ⊕ ι) 𝔸[𝓞 F, F]).1 : ℂ))⁻¹ = _
      rw [hb1, map_mul, Circle.coe_mul, ← hωb, hB.ωχ, mul_comm, ← mul_assoc,
        inv_mul_cancel₀ (Circle.coe_ne_zero _), one_mul]
    · show (A.uH ε Set.univ (j p) - ld p) / 2 = _
      rw [hext p hp, hb1, hGL.lgmul, hB.lg, hl]
      simp only [So.ld]
      rw [hb2, hSG]
      ring

end GlobalTheory.CompanionTheory.EisJMir
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JMapVal
section
noncomputable section

open Matrix PositivityTheory.RgEis PositivityTheory.RgEis.So

namespace GlobalTheory.CompanionTheory.RgEis.Cover

variable {R S : Type} [CommRing R] [CommRing S] {ι : Type} [Fintype ι] [DecidableEq ι]

def sc (a : Rˣ) : GL (ι ⊕ ι) R := Units.map (Matrix.scalar (ι ⊕ ι) : R →+* _).toMonoidHom a

theorem sc_val (a : Rˣ) (G : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :
    ((sc a : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * G = (a : R) • G := by
  show Matrix.scalar (ι ⊕ ι) (a : R) * G = (a : R) • G
  rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]

theorem sc_comm (a : Rˣ) (g : GL (ι ⊕ ι) R) : sc a * g = g * sc a := by
  apply Units.ext
  show Matrix.scalar (ι ⊕ ι) (a : R) * (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) =
    (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * Matrix.scalar (ι ⊕ ι) (a : R)
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, ← Matrix.smul_eq_mul_diagonal]

def jMap (D : GL (ι ⊕ ι) R) (ν : S →+* R) : Rˣ × GL (ι ⊕ ι) S →* GL (ι ⊕ ι) R where
  toFun x := sc x.1 * (D⁻¹ * Matrix.GeneralLinearGroup.map ν x.2 * D)
  map_one' := by
    have : (sc (1 : Rˣ) : GL (ι ⊕ ι) R) = 1 := by simp [sc]
    simp [this]
  map_mul' x y := by
    have h : (sc (x.1 * y.1) : GL (ι ⊕ ι) R) = sc x.1 * sc y.1 := by simp [sc]
    simp only [Prod.fst_mul, Prod.snd_mul, h, map_mul]
    rw [mul_assoc (sc x.1) _ (sc y.1 * _), ← mul_assoc _ (sc y.1), ← sc_comm y.1 (D⁻¹ * Matrix.GeneralLinearGroup.map ν x.2 * D)]
    simp only [mul_assoc, mul_inv_cancel_left]

theorem J_apply (e : ℤˣ) (i : ι) (hi : ∀ x : ι, x = i) (G G' : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (x y : ι ⊕ ι) :
    (Gᵀ * Ad.J R e ι * G') x y =
      G (Sum.inl i) x * G' (Sum.inr i) y + ((e : ℤ) : R) * G (Sum.inr i) x * G' (Sum.inl i) y := by
  have hs : ∀ f : ι → R, ∑ z, f z = f i := fun f =>
    Fintype.sum_eq_single i (fun z hz => (hz (hi z)).elim)
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, hs, Matrix.transpose_apply,
    PositivityTheory.RgEis.Ad.J, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.one_apply_eq, Matrix.smul_apply,
    Matrix.zero_apply, smul_eq_mul]
  ring

theorem det_two (i : ι) (hi : ∀ x : ι, x = i) (N : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :
    N.det = N (Sum.inl i) (Sum.inl i) * N (Sum.inr i) (Sum.inr i) -
      N (Sum.inl i) (Sum.inr i) * N (Sum.inr i) (Sum.inl i) := by
  let e : Fin 2 ≃ ι ⊕ ι :=
    { toFun := ![Sum.inl i, Sum.inr i]
      invFun := Sum.elim (fun _ => 0) (fun _ => 1)
      left_inv := fun x => by fin_cases x <;> rfl
      right_inv := fun x => by
        rcases x with x | x <;> (have h := hi x; subst h; rfl) }
  rw [← Matrix.det_submatrix_equiv_self e N, Matrix.det_fin_two]
  rfl

theorem mem_aux (σ : R →+* R) (e : ℤˣ) (i : ι) (hi : ∀ x : ι, x = i) (a d d' : R)
    (N : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (hN : ∀ x y, σ (N x y) = N x y) (hd : d * d' = 1)
    (hσ : σ d = -(((e : ℤ) : R) * d)) (ha : a * σ a * N.det = 1) :
    (a • (Matrix.diagonal (Sum.elim (fun _ : ι => (1 : R)) fun _ => d') * N *
        Matrix.diagonal (Sum.elim (fun _ : ι => (1 : R)) fun _ => d)))ᵀ * Ad.J R e ι *
      (a • (Matrix.diagonal (Sum.elim (fun _ : ι => (1 : R)) fun _ => d') * N *
        Matrix.diagonal (Sum.elim (fun _ : ι => (1 : R)) fun _ => d))).map σ = Ad.J R e ι := by
  have he2 : ((e : ℤ) : R) * ((e : ℤ) : R) = 1 := by
    rcases Int.units_eq_one_or e with h | h <;> simp [h]
  have h1 : σ d * σ d' = 1 := by rw [← map_mul, hd, map_one]
  rw [hσ] at h1
  have hσd' : σ d' = -(((e : ℤ) : R) * d') := by
    linear_combination (-(((e : ℤ) : R) * d')) * h1 - (σ d' * ((e : ℤ) : R) ^ 2) * hd - σ d' * he2
  have hdet := GlobalTheory.CompanionTheory.RgEis.Cover.det_two i hi N
  ext x y
  rw [GlobalTheory.CompanionTheory.RgEis.Cover.J_apply e i hi]
  rcases x with x | x <;> rcases y with y | y <;> rw [hi x, hi y] <;>
    simp only [Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply,
      Sum.elim_inl, Sum.elim_inr, smul_eq_mul, map_mul, map_one, hN, hσ, hσd', one_mul, mul_one,
      PositivityTheory.RgEis.Ad.J, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.one_apply_eq]
  · ring
  · linear_combination (((e : ℤ) : R) ^ 2 * a * σ a * (N (Sum.inl i) (Sum.inl i) * N (Sum.inr i) (Sum.inr i) -
        N (Sum.inl i) (Sum.inr i) * N (Sum.inr i) (Sum.inl i))) * hd +
      (a * σ a * (N (Sum.inl i) (Sum.inl i) * N (Sum.inr i) (Sum.inr i) -
        N (Sum.inl i) (Sum.inr i) * N (Sum.inr i) (Sum.inl i))) * he2 + ha - (a * σ a) * hdet
  · linear_combination (((e : ℤ) : R) * a * σ a * (N (Sum.inl i) (Sum.inl i) * N (Sum.inr i) (Sum.inr i) -
        N (Sum.inl i) (Sum.inr i) * N (Sum.inr i) (Sum.inl i))) * hd +
      ((e : ℤ) : R) * ha - (((e : ℤ) : R) * a * σ a) * hdet
  · ring

theorem jMap_val (D : GL (ι ⊕ ι) R) (ν : S →+* R) (x : Rˣ × GL (ι ⊕ ι) S) :
    ((jMap D ν x : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) =
      (x.1 : R) • ((D⁻¹ * Matrix.GeneralLinearGroup.map ν x.2 * D : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) := by
  show ((GlobalTheory.CompanionTheory.RgEis.Cover.sc x.1 * (D⁻¹ * Matrix.GeneralLinearGroup.map ν x.2 * D) : GL (ι ⊕ ι) R) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) R) = _
  rw [Units.val_mul, GlobalTheory.CompanionTheory.RgEis.Cover.sc_val]

theorem jEx : JEx := by
  intro F E R _ _ _ _ _ _ A ε ν r δ α ω ι _ _ i hD hi
  obtain ⟨-, -, hfix, -, -, -, -, -, -, -, -, -, hδ, -, -⟩ := hD
  refine ⟨((GlobalTheory.CompanionTheory.RgEis.Cover.jMap (PositivityTheory.RgEis.So.dg ι (Units.map (PositivityTheory.RgEis.Ad.i A : E →* R) δ)) ν).comp
    (PositivityTheory.RgEis.So.cover A ν ι).subtype).codRestrict (PositivityTheory.RgEis.Ad.uSub A ε ι) ?_, ?_⟩
  · rintro ⟨⟨a, g⟩, hx⟩
    have h1 : (a : R) * PositivityTheory.RgEis.Ad.σ A (a : R) * ν (g : Matrix (ι ⊕ ι) (ι ⊕ ι) _).det = 1 :=
      congrArg Units.val ((MonoidHom.mem_ker).1 hx)
    have e1 : ((Matrix.GeneralLinearGroup.map ν g : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R).det =
        ν (g : Matrix (ι ⊕ ι) (ι ⊕ ι) _).det := (RingHom.map_det ν _).symm
    have key := GlobalTheory.CompanionTheory.RgEis.Cover.mem_aux (PositivityTheory.RgEis.Ad.σ A) ε i hi (a : R)
      ((Units.map (PositivityTheory.RgEis.Ad.i A : E →* R) δ : Rˣ) : R)
      (((Units.map (PositivityTheory.RgEis.Ad.i A : E →* R) δ)⁻¹ : Rˣ) : R)
      ((Matrix.GeneralLinearGroup.map ν g : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)
      (fun x y => hfix ((g : Matrix (ι ⊕ ι) (ι ⊕ ι) _) x y)) (Units.mul_inv _) hδ (by rw [e1]; exact h1)
    show ((GlobalTheory.CompanionTheory.RgEis.Cover.jMap (PositivityTheory.RgEis.So.dg ι (Units.map (PositivityTheory.RgEis.Ad.i A : E →* R) δ)) ν (a, g) :
        GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)ᵀ * PositivityTheory.RgEis.Ad.J R ε ι *
      ((GlobalTheory.CompanionTheory.RgEis.Cover.jMap (PositivityTheory.RgEis.So.dg ι (Units.map (PositivityTheory.RgEis.Ad.i A : E →* R) δ)) ν (a, g) :
        GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R).map (PositivityTheory.RgEis.Ad.σ A) =
      PositivityTheory.RgEis.Ad.J R ε ι
    rw [GlobalTheory.CompanionTheory.RgEis.Cover.jMap_val]
    exact key
  · intro x
    exact GlobalTheory.CompanionTheory.RgEis.Cover.jMap_val _ _ _

end GlobalTheory.CompanionTheory.RgEis.Cover
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityCuspidalProduct
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspJm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsPermCell {l c : ℕ} (x : Fin l → IrrGL (k := k)) (y : Fin c → IrrGL (k := k))
    (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)) : Prop :=
  ∃ e : Fin c ≃ Fin l, (∀ a, y a = x (e a)) ∧ ∀ i j, b.1 i j = if e j = i then (x i).1 else 0

def permMatrix {l c : ℕ} (x : Fin l → IrrGL (k := k)) (y : Fin c → IrrGL (k := k)) (e : Fin c ≃ Fin l)
    (h : ∀ a, y a = x (e a)) : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1) :=
  ⟨fun i j => if e j = i then (x i).1 else 0, fun i => by
    rw [Finset.sum_eq_single (e.symm i) (fun j _ hj => if_neg fun h' => hj (by rw [← h', e.symm_apply_apply]))
      (by simp)]
    simp, fun j => by
    rw [Finset.sum_ite_eq]
    simp [h j]⟩


set_option maxHeartbeats 2000000 in
theorem exists_choice (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {l c : ℕ} (x : Fin l → IrrGL (k := k)) (y : Fin c → IrrGL (k := k)) :
    ∃ (f : ∀ (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)) i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1)
      (g : ∀ (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)) j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1),
      ∀ b, IsPermCell x y b →
        jhMult (piTensor fun j => (y j).rep) (cellFunctor (f b) (g b) (piTensor fun i => (x i).rep)) = 1 := by
  classical
  have key : ∀ b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1), IsPermCell x y b → ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1)
      (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1),
      jhMult (piTensor fun j => (y j).rep) (cellFunctor f g (piTensor fun i => (x i).rep)) = 1 := by
    rintro b ⟨e, he, hb⟩
    exact GlobalTheory.T.size_matrix_permutation_equivs_exist hA x y e he b hb
  have key' : ∀ b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1), ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1),
      IsPermCell x y b → jhMult (piTensor fun j => (y j).rep) (cellFunctor f g (piTensor fun i => (x i).rep)) = 1 := by
    intro b
    by_cases h : IsPermCell x y b
    · obtain ⟨f, g, hfg⟩ := key b h
      exact ⟨f, g, fun _ => hfg⟩
    · exact ⟨b.nonempty_rows.some, b.nonempty_cols.some, fun h' => absurd h' h⟩
  choose f g hfg using key'
  exact ⟨f, g, hfg⟩

theorem card_permCell {l c : ℕ} (x : Fin l → IrrGL (k := k)) (y : Fin c → IrrGL (k := k)) (hxc : ∀ a, (x a).IsCusp)
    [Fintype (SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1))] [DecidablePred (IsPermCell x y)] :
    (Finset.univ.filter (IsPermCell x y)).card = Set.ncard {e : Fin c ≃ Fin l | ∀ a, y a = x (e a)} := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  symm
  refine Finset.card_bij (fun e he => permMatrix x y e (Set.mem_toFinset.1 he)) ?_ ?_ ?_
  · intro e he
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, e, Set.mem_toFinset.1 he, fun i j => rfl⟩
  · intro e he e' he' H
    refine Equiv.ext fun j => ?_
    have h2 := congrArg (fun b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1) => b.1 (e j) j) H
    simp only [permMatrix, if_true] at h2
    by_contra hne
    rw [if_neg (Ne.symm hne)] at h2
    exact (hxc (e j)).1.ne' h2
  · intro b hb
    obtain ⟨e, he, hb⟩ := (Finset.mem_filter.1 hb).2
    exact ⟨e, Set.mem_toFinset.2 he, Subtype.ext (funext fun i => funext fun j => (hb i j).symm)⟩


set_option maxHeartbeats 1000000 in
theorem main (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {l c N : ℕ} (x : Fin l → IrrGL (k := k)) (y : Fin c → IrrGL (k := k))
    (hx : ∑ a, (x a).1 = N) (hy : ∑ a, (y a).1 = N) (hxc : ∀ a, (x a).IsCusp) (hyc : ∀ a, (y a).IsCusp) :
    jm y hy (prodIrr x hx) = (Set.ncard {e : Fin c ≃ Fin l | ∀ a, y a = x (e a)} : ℕ∞) := by
  classical
  haveI : Fintype (SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)) := Fintype.ofFinite _
  obtain ⟨f, g, hfg⟩ := exists_choice hA x y
  have hτ : (piTensor fun j => (y j).rep).IsIrreducible :=
    _root_.GlobalTheory.ExtTensorIrr.piTensor_isIrreducible GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k _ _ fun j => (y j).2.rep
  have h1 := (GlobalTheory.CompanionTheory.GeoLink.geometricLemma k).1.jhMult_eq (stdBlocks (fun a => (x a).1) hx)
    (stdBlocks (fun a => (y a).1) hy) (isSmooth_piTensor fun i => (x i).2.rep.smooth) f g hτ
  have hterm : ∀ b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1), jhMult (piTensor fun j => (y j).rep) (cellFunctor (f b) (g b) (piTensor fun i => (x i).rep)) =
      if IsPermCell x y b then 1 else 0 := by
    intro b
    split_ifs with h
    · exact hfg b h
    · by_contra hne
      exact h (GlobalTheory.T.cuspidal_cell_multiplicity_of_size_matrix x y hxc hyc b (f b) (g b) hne)
  have h2 : jm y hy (prodIrr x hx) = jhMult (piTensor fun j => (y j).rep)
      (GlobalTheory.SmGL.jac (stdBlocks (fun a => (y a).1) hy) (parInd (stdBlocks (fun a => (x a).1) hx)
        (piTensor fun i => (x i).rep))) := rfl
  rw [h2, h1, Finset.sum_congr rfl fun b _ => hterm b, Finset.sum_boole, card_permCell x y hxc]

end GlobalTheory.CompanionTheory.CuspJm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitKA
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.CompanionTheory.IwaAd

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

variable {D : D7} {n : ℕ}

def whitT (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (μ : Measure (Mx D V.rank n)) (lam : Measure (hermA D n))
    (nb : hermA D n → G D n) (w : G D n) (H : G D n → ℝ≥0) (φ : Mx D V.rank n → ℂ) (T : Mx D n n) (g : G D n) :
    ℂ → ℂ :=
  fun z => ∫ b, npow (H (w * nb b * g)) (z - s0 V n) * Jt ψ V μ φ b *
    ψ (-halfTr (Matrix.trace (HMul.hMul T b.1 : Mx D n n))) ∂lam

def WhitKA : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
  ∀ (lam : Measure (hermA D n)) (𝓖 : Set (hermA D n)) (nb : hermA D n → G D n), CoefData nb lam 𝓖 →
  ∀ w : G D n, mat w = blk4 0 1 (-1) 0 → ∀ (β : HermE D n), β.1.det ≠ 0 →
  ∀ a : GL (Fin n) (AE D), ∀ k ∈ K D n,
    HolValueAt (whitT ψ V μ lam nb w H (ω k Φ).1 (adj a.1 * β.1.map (incA D) * a.1) k) (s0 V n)
      (npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) - n) *
        IfrB V ν (fun x => (ω k Φ).1 (HMul.hMul x a.1)) β)

end GlobalTheory.CompanionTheory.IwaAd
end
end

