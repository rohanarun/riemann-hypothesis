module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0316
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PhiTTransport
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0342

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceCouplingIndexFiniteLevelStable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QPl.CoupStab
open GlobalTheory.StepData GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mulVec_mem_box {n : Type} [Fintype n] {M : Matrix n n k} (hM : IntM M) {c : kˣ} {y : n → k}
    (hy : y ∈ box n c) : M *ᵥ y ∈ box n c := by
  rw [mem_box] at hy ⊢
  intro i
  simp only [Matrix.mulVec, dotProduct]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_of_le_one_of_le (hM i j) (hy j)

theorem toBlocks₁₁_mul {n : Type} [Fintype n] (M N : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k) :
    (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ := by
  ext i j; simp [Matrix.mul_apply, Matrix.toBlocks₁₁, Fintype.sum_sum_type]

theorem toBlocks₁₁_one {n : Type} [Fintype n] [DecidableEq n] :
    (1 : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k).toBlocks₁₁ = 1 := by
  ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]

theorem withCol_mul {n n' : Type} [Fintype n] (κ : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k) (x₀ : Matrix n n' k)
    (y : n → k) : κ * withCol x₀ y = withCol (κ.toBlocks₁₁ * x₀) (κ.toBlocks₁₁ *ᵥ y) := by
  ext (r | r) (c | c)
  · simp [withCol, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₁]
  · simp [withCol, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₁, Matrix.mulVec, dotProduct]
  · exact r.elim0
  · exact r.elim0

theorem box_eq_preimage {n : Type} (c : kˣ) :
    (box n c : Set (n → k)) = (fun y : n → k => ((c⁻¹ : kˣ) : k) • y) ⁻¹' Set.pi Set.univ fun _ => (𝒪[k] : Set k) := by
  ext y
  simp only [SetLike.mem_coe, mem_box, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Pi.smul_apply,
    smul_eq_mul]
  refine forall_congr' fun i => ?_
  rw [Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
  have hc : 0 < valuation k (c : k) := by
    rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).2 c.ne_zero
  rw [inv_mul_le_iff₀ hc, mul_one]

theorem isOpen_box {n : Type} [Fintype n] (c : kˣ) : IsOpen (box n c : Set (n → k)) := by
  rw [box_eq_preimage]
  exact (isOpen_set_pi Set.finite_univ fun _ _ => (valuation k).isOpen_integer).preimage (continuous_const_smul _)

theorem isCompact_box {n : Type} [Fintype n] (c : kˣ) : IsCompact (box n c : Set (n → k)) := by
  have hK : IsCompact (𝒪[k] : Set k) := isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace 𝒪[k]))
  have e : (box n c : Set (n → k)) = (fun y : n → k => (c : k) • y) '' Set.pi Set.univ fun _ => (𝒪[k] : Set k) := by
    rw [box_eq_preimage, Set.image_eq_preimage_of_inverse]
    · intro y; simp [smul_smul]
    · intro y; simp [smul_smul]
  rw [e]
  exact (isCompact_univ_pi fun _ => hK).image (continuous_const_smul _)

theorem finite_image_box {n : Type} [Fintype n] (c₁ c₂ : kˣ) :
    ((Submodule.Quotient.mk (p := box n c₂)) '' (box n c₁ : Set (n → k))).Finite := by
  obtain ⟨t, -, ht⟩ := (isCompact_box (n := n) c₁).elim_nhds_subcover
    (fun y => (fun z => z - y) ⁻¹' (box n c₂ : Set (n → k)))
    (fun y _ => ((isOpen_box c₂).preimage (continuous_id.sub continuous_const)).mem_nhds
      (by show y - y ∈ box n c₂; rw [sub_self]; exact zero_mem _))
  refine (t.finite_toSet.image (Submodule.Quotient.mk (p := box n c₂))).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 (ht hy)
  refine ⟨z, hz, (Submodule.Quotient.eq _).2 ?_⟩
  rw [← neg_sub]; exact neg_mem hyz

theorem om_one_ne {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (h : GL b k) (Φ : Matrix b a k → ℂ) (x : Matrix b a k) (hx : om μ 1 h Φ x ≠ 0) : Φ ((h⁻¹ : GL b k).val * x) ≠ 0 := by
  unfold om at hx
  have := right_ne_zero_of_mul hx
  simpa using this

theorem om_g_ne {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g : GL a k) (Φ : Matrix b a k → ℂ) (x x' : Matrix b a k) (hx : om μ g 1 Φ x ≠ 0)
    (h : Φ (x * g.val) ≠ 0 → Φ (x' * g.val) ≠ 0) : om μ g 1 Φ x' ≠ 0 := by
  unfold om at *
  simp only [inv_one, Units.val_one, Matrix.one_mul] at *
  exact mul_ne_zero (left_ne_zero_of_mul hx) (h (right_ne_zero_of_mul hx))

end GlobalTheory.QPl.CoupStab

namespace GlobalTheory.QPl.CoupStab
open GlobalTheory.StepData GlobalTheory.SplitWeil

theorem psi_ne {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z] [DecidableEq Z]
    (T : Chain k s X Z) (hL : T.Laws) {κ : GL (X (s + 1) ⊕ Fin 0) k} (hκ : κ ∈ (T.lev (s + 1) 0 rfl).J)
    (g : GL (X s ⊕ Fin (0 + 1)) k) (x₀ : Matrix (X (s + 1)) (X s) k) (y : X (s + 1) → k) (h : T.Psi g x₀ y ≠ 0) :
    T.Psi g (κ.val.toBlocks₁₁ * x₀) (κ.val.toBlocks₁₁ *ᵥ y) ≠ 0 := by
  have hPhi : ∀ x, T.Phi s 0 rfl x ≠ 0 → T.Phi s 0 rfl (κ.val * x) ≠ 0 := by
    intro x hx
    have e := congrFun ((hL.1 s 0 rfl).2 ⟨κ⁻¹, inv_mem hκ⟩) x
    have hr : om (T.mu (s + 1)) 1 (κ⁻¹ : GL (X (s + 1) ⊕ Fin 0) k) (T.Phi s 0 rfl) x ≠ 0 := by
      rw [e, Pi.smul_apply, smul_eq_mul]; exact mul_ne_zero (Units.ne_zero _) hx
    simpa using om_one_ne _ _ _ _ hr
  unfold Chain.Psi at *
  refine om_g_ne _ _ _ _ _ h fun h' => ?_
  rw [← withCol_mul, Matrix.mul_assoc]
  exact hPhi _ h'

theorem coupIdx_stab : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), (Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂)).Finite ∧ (∀ yb, SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb) ∧ (∀ yb yb', SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb' → SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb' yb) ∧ (∀ yb yb' yb'', SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb' → SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb' yb'' → SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb'') ∧ ∀ yb ∈ Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂), ∀ yb', SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb' → yb' ∈ Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂) := by
  intro D c v χ Q
  have hB : ∀ {g : GL (Q.X (Q.s + 1) ⊕ Fin 0) Q.k}, g ∈ (Q.T.lev (Q.s + 1) 0 rfl).J → IntM g.val.toBlocks₁₁ :=
    fun hg i j => intM_of_mem_KO (Q.le _ _ _ hg) (.inl i) (.inl j)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (finite_image_box Q.c₁ Q.c₂).subset (by rintro _ ⟨y, hy, rfl, -⟩; exact ⟨y, hy, rfl⟩)
  · intro yb
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ yb
    refine ⟨1, one_mem _, y, rfl, ?_⟩
    rw [Units.val_one, toBlocks₁₁_one, Matrix.one_mulVec]
  · rintro _ _ ⟨g, hg, y, rfl, rfl⟩
    refine ⟨g⁻¹, inv_mem hg, _, rfl, ?_⟩
    rw [Matrix.mulVec_mulVec, ← toBlocks₁₁_mul, Units.inv_mul, toBlocks₁₁_one, Matrix.one_mulVec]
  · rintro _ _ _ ⟨g, hg, y, rfl, h1⟩ ⟨g', hg', y', h2, h3⟩
    refine ⟨g' * g, mul_mem hg' hg, y, rfl, ?_⟩
    rw [← h3, Units.val_mul, toBlocks₁₁_mul, ← Matrix.mulVec_mulVec]
    refine (Submodule.Quotient.eq _).2 ?_
    rw [← Matrix.mulVec_sub]
    exact mulVec_mem_box (hB hg') ((Submodule.Quotient.eq _).1 (h1.trans h2.symm))
  · rintro _ ⟨y₁, -, rfl, g, hg, x₀, hΨ⟩ _ ⟨κ, hκ, y, hy, rfl⟩
    have hd : y - y₁ ∈ box _ Q.c₂ := (Submodule.Quotient.eq _).1 hy
    have hΨy : Q.T.Psi g x₀ y ≠ 0 := by
      rw [show y = y₁ + (y - y₁) by abel, (Q.adapt g hg x₀ y₁).2 _ hd]; exact hΨ
    exact ⟨_, mulVec_mem_box (hB hκ) ((Q.adapt g hg x₀ y).1 hΨy), rfl, g, hg, _,
      psi_ne Q.T Q.laws hκ g x₀ y hΨy⟩

end GlobalTheory.QPl.CoupStab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceLastTwoLevelIndicesNeZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QPl

theorem relIndex_KO_ne_zero {k n : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Fintype n] [DecidableEq n] (J : Subgroup (GL n k)) (hJ : IsOpen (J : Set (GL n k))) : J.relIndex (KO k n) ≠ 0 := by
  haveI : CompactSpace (KO k n) := isCompact_iff_compactSpace.1 (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := n))
  haveI : Finite (KO k n ⧸ J.subgroupOf (KO k n)) :=
    Subgroup.quotient_finite_of_isOpen _ (hJ.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

theorem QAt.idx_last_ne_zero : ∀ (D : D7) (c : Comm D) (v : VCom c) (χ : ℕ → (AE D)ˣ →* Circle) (Q : QAt v χ), Q.idx (Q.s + 1) ≠ 0 ∧ Q.idx (Q.s + 1 + 1) ≠ 0 := by
  intro D c v χ Q
  refine ⟨?_, ?_⟩
  · rw [Q.idx_mid (Q.s + 1) 0 rfl]
    exact relIndex_KO_ne_zero _ (Q.reg.2.2 _ _ _).1
  · rw [Q.idx_top]
    exact relIndex_KO_ne_zero _ Q.openT

end GlobalTheory.QPl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceNormalisedCombinationsPreserveThetaFun
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QPl.ThetaPin

variable {D : D7}

theorem isFinComb_of_half {S T : HSp D} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) (c : WO S T →₀ ℂ)
    (hc : ∀ u ∈ c.support, IsHalf (algebraMap (AF D.host.F) (AE D) ε) u) : IsFinComb c := by
  intro u hu
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
    obtain ⟨α, rfl, -, -⟩ := hε
    show infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    simp only [infPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
    show (fstA D.host.F (pairA D.host.F 0 α)) ⊗ₜ[D.host.F] _ = 0
    rw [show fstA D.host.F (pairA D.host.F 0 α) = 0 from rfl, TensorProduct.zero_tmul]
  ext i j
  simp only [Matrix.map_apply, Matrix.zero_apply]
  rw [← hc u hu i j, map_mul, h0, zero_mul]

theorem aconv_support {G : Type} [AddMonoid G] (P : AddSubmonoid G) :
    ∀ (l : List (G →₀ ℂ)), (∀ e ∈ l, ∀ g ∈ e.support, g ∈ P) → ∀ g ∈ (aconv l).support, g ∈ P
  | [], _, g, hg => by
    have : g = 0 := by
      simpa [aconv] using Finsupp.support_single_subset hg
    rw [this]; exact P.zero_mem
  | e :: l, hl, g, hg => by
    classical
    have ih := aconv_support P l (fun e' he' => hl e' (List.mem_cons_of_mem _ he'))
    have he := hl e List.mem_cons_self
    change g ∈ (e.sum fun g a => (aconv l).sum fun h b => Finsupp.single (g + h) (a * b)).support at hg
    have houter : g ∈ e.support.biUnion
        (fun x => ((aconv l).sum fun y b => Finsupp.single (x + y) (e x * b)).support) :=
      Finsupp.support_sum (f := e)
        (g := fun x a => (aconv l).sum fun y b => Finsupp.single (x + y) (a * b)) hg
    rcases Finset.mem_biUnion.mp houter with ⟨x, hx, hg⟩
    have hinner : g ∈ (aconv l).support.biUnion
        (fun y => (Finsupp.single (x + y) (e x * aconv l y)).support) :=
      Finsupp.support_sum (f := aconv l) (g := fun y b => Finsupp.single (x + y) (e x * b)) hg
    rcases Finset.mem_biUnion.mp hinner with ⟨y, hy, hg⟩
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hg)]
    exact P.add_mem (he x hx) (ih y hy)

def finSub (S T : HSp D) : AddSubmonoid (WO S T) where
  carrier := {u | u.map (infPart D) = 0}
  zero_mem' := by ext i j; simp
  add_mem' {a b} ha hb := by
    change Matrix.map a (infPart D) = 0 at ha
    change Matrix.map b (infPart D) = 0 at hb
    change Matrix.map (a + b) (infPart D) = 0
    rw [Matrix.map_add (infPart D) (fun x y => RingHom.map_add (infPart D) x y) a b, ha, hb, add_zero]

theorem isFinComb_aconv {S T : HSp D} (l : List (WO S T →₀ ℂ)) (hl : ∀ e ∈ l, IsFinComb e) : IsFinComb (aconv l) :=
  aconv_support (finSub S T) l hl

theorem isFinComb_cast {c : Comm D} {a b : ℕ} (e : a = b) (x : WO (c.V (a + 1)) c.T →₀ ℂ) (hx : IsFinComb x) :
    IsFinComb (e ▸ x : WO (c.V (b + 1)) c.T →₀ ℂ) := by
  subst e; exact hx

end GlobalTheory.QPl.ThetaPin

open GlobalTheory.QPl.ThetaPin in
theorem GlobalTheory.QPl.pins_keep_theta : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → F.Pins w → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (Ψ₁ : WO (c.V j) (c.V (j + 1)) → ℂ) (Ψ₂ : WO (c.V (j + 1)) c.T → ℂ), IsThetaFunO c.ψ _ _ Ψ₁ → IsThetaFunO c.ψ _ _ Ψ₂ → IsThetaFunO c.ψ _ _ (comb c.ψ _ _ (w.eQ j) Ψ₁) ∧ IsThetaFunO c.ψ _ _ (comb c.ψ _ _ (w.eQT j h) Ψ₂) := by
  intro D c v t w F hc hP j h Ψ₁ Ψ₂ h1 h2
  have hs : ∀ i, (F.Q i).s = j := fun i => by have := (F.Q i).hs; omega
  refine ⟨?_, ?_⟩
  · rw [hP.eQ j (by omega)]
    refine (GlobalTheory.HeisComb.main D c.ψ _ _).2.2.1 _ _ h1 ?_ hc.std
    refine isFinComb_aconv _ fun e he => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
    obtain ⟨ε, hε, hsum⟩ := (F.Q i).q.above
    have hat := ((F.Q i).eL_at j 0 (by have := hs i; omega)).1
    exact isFinComb_of_half hε _ fun u hu => hsum ▸ hat u hu
  · rw [hP.eQT j h]
    refine (GlobalTheory.HeisComb.main D c.ψ _ _).2.2.1 _ _ h2 ?_ hc.std
    refine isFinComb_aconv _ fun e he => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
    obtain ⟨ε, hε, hsum⟩ := (F.Q i).q.above
    have hat := (F.Q i).eLT_at.1
    unfold QAt.eT
    exact isFinComb_cast _ _ (isFinComb_of_half hε _ fun u hu => hsum ▸ hat u hu)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPrimeCongruentMapsFrameReadingsBound
section
noncomputable section

namespace GlobalTheory.Transport.TwistRead

section Gen

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix
open GlobalTheory.Transport.LevelDatum

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] {hc : Formalism.BasicNotions.CMData F E}
  {a b : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

omit [NumberField E] [StarRing E] in
theorem toMatrix_inFr (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b) (x : HomE E a b) :
    LinearMap.toMatrix' f'.toLinearMap * LinearMap.toMatrix' (inFr f f' x) = LinearMap.toMatrix' x * LinearMap.toMatrix' f.toLinearMap := by
  rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
  exact congrArg _ (LinearMap.ext fun z => f'.apply_symm_apply _)

theorem map_ptFr {n : ℕ} {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) {P : HeightOneSpectrum (𝓞 E)}
    (hPQ : P ∈ Q) (hPG : P ∉ SG) :
    (LinearMap.toMatrix' (ptFr p P).toLinearMap).map (algebraMap E (P.adicCompletion E)) =
      (g : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P) := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.map_apply, Matrix.map_apply, LinearMap.toMatrix'_apply, ptFr_of_mem p hPG hPQ]
  exact (h.fr ⟨P, hPQ⟩ i j).symm

omit [StarRing E] in
theorem map_inv_mul_map {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) (AfE F E)) :
    ((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P) *
      (g : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P) = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem map_read {g : GL (Fin a) (AfE F E)} {g' : GL (Fin b) (AfE F E)} {p : DecoF E a ST SG Q} {p' : DecoF E b ST SG Q}
    (h : IsPtOf hc g p) (h' : IsPtOf hc g' p') {P : HeightOneSpectrum (𝓞 E)} (hPQ : P ∈ Q) (hPG : P ∉ SG) (x : HomE E a b) :
    (LinearMap.toMatrix' (inFr (ptFr p P) (ptFr p' P) x)).map (algebraMap E (P.adicCompletion E)) =
      (mid g g' x).map (adAt F P) := by
  have f1 := congrArg (fun A => Matrix.map A (algebraMap E (P.adicCompletion E))) (toMatrix_inFr (ptFr p P) (ptFr p' P) x)
  simp only [Matrix.map_mul] at f1
  rw [map_ptFr h hPQ hPG, map_ptFr h' hPQ hPG] at f1
  have hx : (LinearMap.toMatrix' x).map (algebraMap E (P.adicCompletion E)) = (adMat F x).map (adAt F P) :=
    Matrix.ext fun i j => (adAt_inclE F P _).symm
  unfold mid
  rw [Matrix.map_mul, Matrix.map_mul, ← hx, Matrix.mul_assoc, ← f1, ← Matrix.mul_assoc, map_inv_mul_map, Matrix.one_mul]

theorem read_sub_le {k y : GL (Fin a) (AfE F E)} {k' y' : GL (Fin b) (AfE F E)} {p q : DecoF E a ST SG Q} {p' q' : DecoF E b ST SG Q}
    (hp : IsPtOf hc k p) (hpN : p.deco.1.N = stdLat E a) (hp' : IsPtOf hc k' p') (hpN' : p'.deco.1.N = stdLat E b)
    (hq : IsPtOf hc (y * k) q) (hq' : IsPtOf hc (y' * k') q') {P : HeightOneSpectrum (𝓞 E)} (hPQ : P ∈ Q) (hPG : P ∉ SG)
    (M₀ : ℕ) (x x₀ : HomE E a b)
    (h : ∀ r s, Valued.v (adAt F P ((mid y y' x - adMat F x₀) r s)) ≤ Valued.v ((M₀ : ℕ) : P.adicCompletion E)) (r : Fin b) (s : Fin a) :
    P.valuation E ((LinearMap.toMatrix' (inFr (ptFr q P) (ptFr q' P) x) - LinearMap.toMatrix' (inFr (ptFr p P) (ptFr p' P) x₀)) r s) ≤
      P.valuation E ((M₀ : ℕ) : E) := by
  have hd : mid (y * k) (y' * k') x - mid k k' x₀ =
      ((k'⁻¹ : GL (Fin b) (AfE F E)) : Matrix (Fin b) (Fin b) (AfE F E)) * (mid y y' x - adMat F x₀) *
        (k : Matrix (Fin a) (Fin a) (AfE F E)) := by
    unfold mid
    rw [_root_.mul_inv_rev, Units.val_mul, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_assoc]
  have hA : ∀ r s, Valued.v (adAt F P (((k'⁻¹ : GL (Fin b) (AfE F E)) : Matrix (Fin b) (Fin b) (AfE F E)) r s)) ≤ 1 := fun r s => by
    have := Splice.valued_inv_mul_le (w := P) (hpN' ▸ hp'.lat) (carries_one (F := F) b) le_rfl r s
    rwa [mul_one] at this
  have hK : ∀ r s, Valued.v (adAt F P ((k : Matrix (Fin a) (Fin a) (AfE F E)) r s)) ≤ 1 := fun r s => by
    have := Splice.valued_inv_mul_le (w := P) (carries_one (F := F) a) (hpN ▸ hp.lat) le_rfl r s
    rwa [inv_one, one_mul] at this
  have e1 := congrFun (congrFun (map_read hq hq' hPQ hPG x) r) s
  have e2 := congrFun (congrFun (map_read hp hp' hPQ hPG x₀) r) s
  simp only [Matrix.map_apply] at e1 e2
  rw [← valued_algebraMap, ← valued_algebraMap, map_natCast, Matrix.sub_apply, map_sub, e1, e2, ← map_sub, ← Matrix.sub_apply, hd]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mul_apply, map_sum]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul, map_mul]
  refine (mul_le_of_le_one_right' (hK j s)).trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mul_apply, map_sum]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul, map_mul]
  exact (mul_le_of_le_one_left' (hA r l)).trans (h l j)

end Gen

end GlobalTheory.Transport.TwistRead

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Ker

namespace GlobalTheory.Transport.TwistRead

theorem qread : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι) (i : ℕ) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a)),
    P.1 ∈ I.Q a → Disjoint (B.primes X).vGs (I.Q a) →
    ∀ (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1))
    (k y : TC.GA B (B.R.N i)) (k' y' : TC.GA B (B.R.N (i + 1))),
    TC.PtOf k p.1.1 → p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i) →
    TC.PtOf k' p'.1.1 → p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i + 1)) →
    TC.PtOf (y * k) q.1.1 → TC.PtOf (y' * k') q'.1.1 →
    ∀ (M₀ : ℕ) (x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1))),
      GlobalTheory.Transport.CongAt B P.1 M₀ y y' x x₀ →
      ∀ r s, P.1.valuation B.fields.E
        ((LinearMap.toMatrix' (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x) -
          LinearMap.toMatrix' (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀)) r s) ≤
        P.1.valuation B.fields.E ((M₀ : ℕ) : B.fields.E) := by
  intro B X I u a i P hP hd p q p' q' k y k' y' hp hpN hp' hpN' hq hq' M₀ x x₀ hC r s
  rw [frsF_eq_ptFr, frsF_eq_ptFr, frsF_eq_ptFr, frsF_eq_ptFr]
  exact read_sub_le hp hpN hp' hpN' hq hq' hP (Finset.disjoint_right.1 hd hP) M₀ x x₀ (fun r s => hC r s) r s

end GlobalTheory.Transport.TwistRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryIdempotentCutMemFourierJacobiBesselGroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.SetCut

theorem smul_add_one_sub_smul_sub_one {R : Type} [CommRing R] {n : ℕ} (c : R) (M : Matrix (Fin n) (Fin n) R) :
    c • M + (1 - c) • (1 : Matrix (Fin n) (Fin n) R) - 1 = c • (M - 1) := by
  rw [sub_smul, one_smul, smul_sub]; abel

theorem smul_add_one_sub_smul_block {R : Type} [CommRing R] {n m : ℕ} (c : R) (P Q : Matrix (Fin n) (Fin n) R)
    (j : Matrix (Fin n) (Fin m) R) (p : Matrix (Fin m) (Fin n) R) (M : Matrix (Fin m) (Fin m) R)
    (h : P + j * p + Q = 1) :
    c • (P + j * M * p + Q) + (1 - c) • (1 : Matrix (Fin n) (Fin n) R) =
      P + j * (c • M + (1 - c) • (1 : Matrix (Fin m) (Fin m) R)) * p + Q := by
  rw [← h]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_add, sub_smul,
    one_smul, Matrix.mul_sub, Matrix.sub_mul]
  abel

theorem smul_add_one_sub_smul_block₂ {R : Type} [CommRing R] {n m k : ℕ} (c : R)
    (j : Matrix (Fin n) (Fin m) R) (p : Matrix (Fin m) (Fin n) R) (M : Matrix (Fin m) (Fin m) R)
    (j' : Matrix (Fin n) (Fin k) R) (p' : Matrix (Fin k) (Fin n) R)
    (h : j * p + j' * p' = 1) :
    c • (j * M * p + j' * (1 : Matrix (Fin k) (Fin k) R) * p') + (1 - c) • (1 : Matrix (Fin n) (Fin n) R) =
      j * (c • M + (1 - c) • (1 : Matrix (Fin m) (Fin m) R)) * p + j' * (1 : Matrix (Fin k) (Fin k) R) * p' := by
  have := smul_add_one_sub_smul_block c 0 (j' * p') j p M (by rw [zero_add, h])
  simpa only [zero_add, Matrix.mul_one] using this

variable {D : D7}

theorem jac_subOne_cutG (V : HSp D) (ε : AF D.host.F) (hε : ε * ε = ε) (g : GA D V) :
    Formalism.L2.Theta.subOne V (cutG V ε hε g) = algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.subOne V g :=
  smul_add_one_sub_smul_sub_one (algebraMap (AF D.host.F) (AE D) ε) (Formalism.L2.Theta.mt V g)

theorem jac_cutG_map_NFlag (V : HSp D) {ρ : ℕ} (e : Matrix (Fin V.rank) (Fin ρ) D.host.E) (ε : AF D.host.F)
    (hε : ε * ε = ε) : (NFlag V e).map (cutG V ε hε) ≤ NFlag V e := by
  unfold NFlag
  rw [MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro _ ⟨g, ⟨h1, h2⟩, rfl⟩
  refine ⟨fun i => ?_, fun x hx => ?_⟩
  · obtain ⟨a, ha, hb⟩ := h1 i
    refine ⟨algebraMap (AF D.host.F) (AE D) ε • a, fun j hj => ?_, ?_⟩
    · rw [Pi.smul_apply, ha j hj, smul_zero]
    · rw [jac_subOne_cutG, Matrix.smul_mulVec, hb, Matrix.mulVec_smul]
  · obtain ⟨a, hb⟩ := h2 x hx
    refine ⟨algebraMap (AF D.host.F) (AE D) ε • a, ?_⟩
    rw [jac_subOne_cutG, Matrix.smul_mulVec, hb, Matrix.mulVec_smul]

theorem unitaryIdempotentCut_wittHyperbolicEmbedding_comm {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (ε : AF D.host.F) (hε : ε * ε = ε) (h : GA D V₀) :
    cutG V ε hε (d.emb0 h) = d.emb0 (cutG V₀ ε hε h) := by
  apply GlobalTheory.MixModel.mt_injective V
  change Formalism.L2.Theta.mt V (cutG V ε hε (d.emb0 h)) = Formalism.L2.Theta.mt V (d.emb0 (cutG V₀ ε hε h))
  rw [mt_cutG, HypDec.unitaryMatrix_wittCoreEmbedding, HypDec.unitaryMatrix_wittCoreEmbedding, mt_cutG]
  exact smul_add_one_sub_smul_block _ _ _ _ _ _ d.sum_eq_one

theorem jac_cutG_emb_inl {V₀ A L : HSp D} (o : OrthDec V₀ A L) (ε : AF D.host.F) (hε : ε * ε = ε) (h : GA D A) :
    cutG V₀ ε hε (o.emb (h, 1)) = o.emb (cutG A ε hε h, 1) := by
  apply GlobalTheory.MixModel.mt_injective V₀
  change Formalism.L2.Theta.mt V₀ (cutG V₀ ε hε (o.emb (h, 1))) = Formalism.L2.Theta.mt V₀ (o.emb (cutG A ε hε h, 1))
  rw [mt_cutG, OrthDec.mt_emb, OrthDec.mt_emb, mt_cutG, mt_one]
  exact smul_add_one_sub_smul_block₂ _ _ _ _ _ _ o.sum_eq_one

theorem cutG_mem_jacGrp_besGrp (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (ε : AF D.host.F) (hε : ε * ε = ε) :
    (∀ g ∈ jacGrp d, cutG V ε hε g ∈ jacGrp d) ∧
      ∀ (A L : HSp D) (o : OrthDec V₀ A L), ∀ g ∈ besGrp d o, cutG V ε hε g ∈ besGrp d o := by
  refine ⟨fun g hg => ?_, fun A L o g hg => ?_⟩
  · have H : (jacGrp d).map (cutG V ε hε) ≤ jacGrp d := by
      unfold jacGrp
      rw [Subgroup.map_sup]
      refine sup_le_sup (jac_cutG_map_NFlag V d.e ε hε) ?_
      rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
      exact ⟨cutG V₀ ε hε h, (unitaryIdempotentCut_wittHyperbolicEmbedding_comm d ε hε h).symm⟩
    exact H ⟨g, hg, rfl⟩
  · have H : (besGrp d o).map (cutG V ε hε) ≤ besGrp d o := by
      unfold besGrp
      rw [Subgroup.map_sup]
      refine sup_le_sup (jac_cutG_map_NFlag V d.e ε hε) ?_
      rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
      refine ⟨cutG A ε hε h, ?_⟩
      rw [embA_apply, embA_apply, unitaryIdempotentCut_wittHyperbolicEmbedding_comm, jac_cutG_emb_inl]
    exact H ⟨g, hg, rfl⟩

end GlobalTheory.FinPl.SetCut

end
end

