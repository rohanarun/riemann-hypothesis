module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0612
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0083
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0196
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0193
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSstAtOfIsCrysAt
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.CrysSst

open Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PMon Module TensorProduct

theorem finrank_Dst_le {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    {K : FinExt l} {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    (ρ : Representation ℚ_[l] ↥(GK K) V) :
    FiniteDimensional ℚ_[l] ↥(Dst P ρ) ∧
      finrank ℚ_[l] ↥(Dst P ρ) ≤ finrank ℚ_[l] V * finrank ℚ_[l] ↥(K0 K) := by
  obtain ⟨hdom, hreg, -⟩ := GlobalTheory.Pst.stRegular l P AI ⟨T⟩
  have hup := GlobalTheory.PstRank.rank_DpstUr_le P hdom hreg ρ
  haveI : FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) :=
    Module.rank_lt_aleph0_iff.mp (hup.trans_lt Cardinal.natCast_lt_aleph0)
  have hup' : finrank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) ≤ finrank ℚ_[l] V := by
    rw [← finrank_eq_rank] at hup
    exact_mod_cast hup
  haveI := K.2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective inf_le_left)
  let val : DpstUr P ρ →+ V ⊗[ℚ_[l]] Bst P :=
    (Dpst P ρ).subtype.toAddMonoidHom.comp (toUr P ρ).symm.toAddMonoidHom
  have hSD : Dst P ρ ≤ Dpst P ρ := fun s hs => (mem_Dpst P ρ).mpr ⟨K, fun g _ => (mem_Dst P ρ).mp hs g⟩
  obtain ⟨b, hbS, hsp, hli⟩ := exists_linearIndependent ↥(MaximalUnramifiedExtension l) {y : DpstUr P ρ | val y ∈ Dst P ρ}
  haveI : Finite ↥b := hli.finite
  letI : Fintype ↥b := Fintype.ofFinite _
  have hspan : ∀ y : DpstUr P ρ, y ∈ Submodule.span ↥(MaximalUnramifiedExtension l) b → ∃ c : ↥b → ↥(MaximalUnramifiedExtension l),
      ∑ i, c i • (i : DpstUr P ρ) = y := fun y hy => by
    rw [← Submodule.mem_span_range_iff_exists_fun, Subtype.range_coe]; exact hy
  let inc : ↥(K0 K) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l) := IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l)
  let f : (↥b → ↥(K0 K)) →ₗ[ℚ_[l]] V ⊗[ℚ_[l]] Bst P :=
    { toFun := fun c => ∑ i, mulV P ℚ_[l] V (inc (c i)) (val i)
      map_add' := fun c c' => by simp [Finset.sum_add_distrib]
      map_smul' := fun q c => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => mulV_padic_smul P _ V q (inc (c i)) (val i) }
  have hle : Dst P ρ ≤ LinearMap.range f := by
    intro s hs
    obtain ⟨c, hc⟩ := hspan (toUr P ρ ⟨s, hSD hs⟩) (hsp ▸ Submodule.subset_span hs)
    have hfix : ∀ i, (c i : Om l) ∈ K.1 := fun i => mem_of_GK_fixed fun g => by
      have := semilinear_coord_fixed hli (fun a => ⟨_, galois_mem_Kur g a⟩)
        (actD P ρ g).toAddMonoidHom
        (fun a y => LinearMap.congr_fun (actD_mulD P ρ g a _ rfl) y)
        (fun j => Subtype.ext ((mem_Dst P ρ).mp (hbS j.2) g)) c
        (by rw [hc]; exact Subtype.ext ((mem_Dst P ρ).mp hs g)) i
      exact congrArg Subtype.val this
    refine ⟨fun i => ⟨c i, hfix i, (c i).2⟩, ?_⟩
    have := congrArg val hc
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    exact this
  refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
  have h1 : finrank ℚ_[l] ↥(Dst P ρ) ≤ Fintype.card ↥b * finrank ℚ_[l] ↥(K0 K) := by
    refine (Submodule.finrank_mono hle).trans ((LinearMap.finrank_range_le f).trans ?_)
    simp [Module.finrank_pi_fintype]
  exact h1.trans (Nat.mul_le_mul_right _ (hli.fintype_card_le_finrank.trans hup'))

theorem isSst_of_isCrys {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    {K LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (h : IsCrys (P.PD K) ρ) : IsSst P ρ := by
  haveI := LL.2
  haveI : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥LL.1 V
  obtain ⟨hfin, hb⟩ := finrank_Dst_le P AI T (GlobalTheory.PstCoeff.resQ ρ)
  have hD : Dst P (GlobalTheory.PstCoeff.resQ ρ) = (Dst P ρ).restrictScalars ℚ_[l] := by
    ext x
    simp [mem_Dst, GlobalTheory.PstCoeff.stRep_resQ]
  have e : finrank ℚ_[l] ↥(Dst P (GlobalTheory.PstCoeff.resQ ρ)) = finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 ↥(Dst P ρ) := by
    rw [hD, finrank_mul_finrank]
    rfl
  have hfin' : FiniteDimensional ℚ_[l] ↥((Dst P ρ).restrictScalars ℚ_[l]) := hD ▸ hfin
  haveI : Module.Finite ℚ_[l] ↥(Dst P ρ) := hfin'
  haveI : FiniteDimensional ↥LL.1 ↥(Dst P ρ) :=
    Module.Finite.of_restrictScalars_finite ℚ_[l] ↥LL.1 ↥(Dst P ρ)
  have hV : finrank ℚ_[l] V = finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 V := (finrank_mul_finrank ℚ_[l] ↥LL.1 V).symm
  have hup : finrank ↥LL.1 ↥(Dst P ρ) ≤ finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 V := by
    rw [e, hV] at hb
    refine Nat.le_of_mul_le_mul_left ?_ (finrank_pos (R := ℚ_[l]) (M := ↥LL.1))
    calc finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 ↥(Dst P ρ)
        ≤ finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 V * finrank ℚ_[l] ↥(K0 K) := hb
      _ = finrank ℚ_[l] ↥LL.1 * (finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 V) := by ring
  have hle : (Dcris (P.PD K) ρ).map (crisIncl P ↥LL.1 V) ≤ Dst P ρ := fun x hx =>
    ((mem_Dst_and_monV_eq_zero_iff l P K LL V ρ x).mpr hx).1
  have hlo : finrank ↥LL.1 ↥(Dcris (P.PD K) ρ) ≤ finrank ↥LL.1 ↥(Dst P ρ) := by
    rw [(Submodule.equivMapOfInjective _ (crisIncl_injective P) (Dcris (P.PD K) ρ)).finrank_eq]
    exact Submodule.finrank_mono hle
  unfold IsCrys at h
  unfold IsSst
  exact le_antisymm hup (h ▸ hlo)

end GlobalTheory.CrysSst

theorem GlobalTheory.CrysSst.isSstAt_of_isCrysAt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (a : ℕ) (r : ↥Gw →* GL (Fin a) (Om l)), IsCrysAt P Bw r → IsSstAt P Bw r := by
  intro l _ P AI hT E Ω _ _ _ Gw O _ _ _ Bw a r hc
  obtain ⟨T⟩ := hT
  obtain ⟨LL', r', hm, hcr⟩ := hc
  exact ⟨LL', r', hm, GlobalTheory.CrysSst.isSst_of_isCrys P AI T (Bw.repE LL' r') hcr⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JacquetModuleImageNeZeroOfBlockTypeVector
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.JacBlockTwo

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.JacBlock ValuativeRel Matrix

abbrev sz (r t : ℕ) : Fin 2 → ℕ := ![r, t]

theorem sum_sz (r t : ℕ) : ∑ a, sz r t a = r + t := by simp [sz]

def blocks2 (r t : ℕ) : (Σ a : Fin 2, Fin (sz r t a)) ≃ Fin (r + t) := stdBlocks _ (sum_sz r t)

theorem blocks2_zero (r t : ℕ) (i : Fin r) : blocks2 r t ⟨0, i⟩ = Fin.castAdd t i := by
  ext
  refine (stdBlocks_val (sz r t) (sum_sz r t) 0 i).trans ?_
  simp

theorem blocks2_one (r t : ℕ) (j : Fin t) : blocks2 r t ⟨1, j⟩ = Fin.natAdd r j := by
  ext
  refine (stdBlocks_val (sz r t) (sum_sz r t) 1 j).trans ?_
  simp [sz]

theorem twoE_false (r t : ℕ) (i : Fin r) : two (stdSum (rfl : r + t = r + t)) ⟨false, i⟩ = Fin.castAdd t i := by
  ext; simp

theorem twoE_true (r t : ℕ) (j : Fin t) : two (stdSum (rfl : r + t = r + t)) ⟨true, j⟩ = Fin.natAdd r j := by
  ext; simp

end GlobalTheory.JacBlockTwo

noncomputable section

namespace GlobalTheory.JacBlockTwo

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.JacBlock ValuativeRel Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdSum_inl' (r t : ℕ) (i : Fin r) : stdSum (rfl : r + t = r + t) (Sum.inl i) = Fin.castAdd t i := by
  ext; simp

theorem stdSum_inr' (r t : ℕ) (j : Fin t) : stdSum (rfl : r + t = r + t) (Sum.inr j) = Fin.natAdd r j := by
  ext; simp

def IsUpperUnip {r t : ℕ} (g : GL (Fin (r + t)) k) : Prop :=
  (∀ (i : Fin t) (j : Fin r), (g : Matrix (Fin (r + t)) (Fin (r + t)) k) (Fin.natAdd r i) (Fin.castAdd t j) = 0) ∧
  (∀ i j : Fin r, (g : Matrix (Fin (r + t)) (Fin (r + t)) k) (Fin.castAdd t i) (Fin.castAdd t j) =
    (1 : Matrix (Fin r) (Fin r) k) i j) ∧
  (∀ i j : Fin t, (g : Matrix (Fin (r + t)) (Fin (r + t)) k) (Fin.natAdd r i) (Fin.natAdd r j) =
    (1 : Matrix (Fin t) (Fin t) k) i j)

theorem mem_unipRad_two {r t : ℕ} {g : GL (Fin (r + t)) k} :
    g ∈ unipRad k (two (stdSum (rfl : r + t = r + t))) ↔ IsUpperUnip g := by
  rw [mem_unipRad, mem_parab_two]
  constructor
  · rintro ⟨h0, hD⟩
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · rw [← stdSum_inl', ← stdSum_inr']; exact h0 i j
    · rw [← twoE_false, ← twoE_false]; exact hD false i j
    · rw [← twoE_true, ← twoE_true]; exact hD true i j
  · rintro ⟨h0, h1, h2⟩
    refine ⟨fun j i => ?_, ?_⟩
    · have := h0 j i; rwa [← stdSum_inl', ← stdSum_inr'] at this
    · rintro (_ | _) i j
      · have := h1 i j; rwa [← twoE_false, ← twoE_false] at this
      · have := h2 i j; rwa [← twoE_true, ← twoE_true] at this

theorem mem_unipRad_blocks2 {r t : ℕ} {g : GL (Fin (r + t)) k} :
    g ∈ unipRad k (blocks2 r t) ↔ IsUpperUnip g := by
  rw [mem_unipRad, mem_parab_iff]
  constructor
  · rintro ⟨h0, hD⟩
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · rw [← blocks2_one, ← blocks2_zero]; exact h0 1 0 i j (by decide)
    · rw [← blocks2_zero, ← blocks2_zero]; exact hD 0 i j
    · rw [← blocks2_one, ← blocks2_one]; exact hD 1 i j
  · rintro ⟨h0, h1, h2⟩
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · match a, b with
      | 0, 0 => intro i j hab; exact absurd hab (lt_irrefl _)
      | 0, 1 => intro i j hab; exact absurd hab (by decide)
      | 1, 0 => intro i j _; rw [blocks2_one r t i, blocks2_zero r t j]; exact h0 i j
      | 1, 1 => intro i j hab; exact absurd hab (lt_irrefl _)
    · match a with
      | 0 => intro i j; rw [blocks2_zero r t i, blocks2_zero r t j]; exact h1 i j
      | 1 => intro i j; rw [blocks2_one r t i, blocks2_one r t j]; exact h2 i j

theorem unipRad_blocks2 (r t : ℕ) :
    unipRad k (blocks2 r t) = unipRad k (two (stdSum (rfl : r + t = r + t))) := by
  ext g; rw [mem_unipRad_blocks2, mem_unipRad_two]

theorem unipRad_two_inf_KO_le_stab {r t : ℕ} {χ : kˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin (r + t)) k) W} {v : W} (hv : IsBlockVec χ π v) :
    unipRad k (two (stdSum (rfl : r + t = r + t))) ⊓ KO k (Fin (r + t)) ≤ stab π v := by
  intro h hh
  obtain ⟨h0, h1, h2⟩ := mem_unipRad_two.1 hh.1
  have hsub : h.val.submatrix (Fin.natAdd r) (Fin.natAdd r) = 1 := by ext i j; exact h2 i j
  have key := hv h hh.2 (fun i j => by simp [h0]) (fun i j => by simp [h1, Matrix.one_apply]) 1
    (by rw [hsub, det_one, Units.val_one])
  show π h v = v
  rw [key, map_one, Units.val_one, one_smul]

theorem mulSingle_mem_KO {r t : ℕ} {g : GL (Fin t) k} (hg : g ∈ KO k (Fin t)) (a : Bool) :
    (Pi.mulSingle true g : Levi k (Two (Fin r) (Fin t))) a ∈ KO k (Two (Fin r) (Fin t) a) := by
  cases a
  · rw [Pi.mulSingle_eq_of_ne (by decide)]; exact one_mem _
  · rw [Pi.mulSingle_eq_same]; exact hg

theorem deltaHalf_mulSingle {r t : ℕ} {g : GL (Fin t) k} (hg : g ∈ KO k (Fin t)) :
    deltaHalf k (Two (Fin r) (Fin t)) (Pi.mulSingle true g) = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => isUnram_absPow k _ _ ?_
  exact GlobalTheory.StepData.valuation_det_of_mem_KO (mulSingle_mem_KO (r := r) hg a)

theorem act_mulSingle {r t : ℕ} {χ : kˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin (r + t)) k) W} {v : W} (hv : IsBlockVec χ π v)
    {g : GL (Fin t) k} (hg : g ∈ KO k (Fin t)) :
    π (leviEmb k (two (stdSum (rfl : r + t = r + t))) (Pi.mulSingle true g)) v =
      (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v := by
  set h := leviEmb k (two (stdSum (rfl : r + t = r + t)))
    (Pi.mulSingle true g : Levi k (Two (Fin r) (Fin t))) with hdef
  have hKO : h ∈ KO k (Fin (r + t)) := by
    refine GlobalTheory.StepData.mem_KO.2 ⟨intM_leviEmb _ _ fun a =>
      GlobalTheory.StepData.intM_of_mem_KO (mulSingle_mem_KO hg a), ?_⟩
    rw [hdef, ← map_inv]
    exact intM_leviEmb _ _ fun a => GlobalTheory.StepData.intM_of_mem_KO (inv_mem (mulSingle_mem_KO hg a))
  have h0 : ∀ (i : Fin t) (j : Fin r), h.val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := fun i j => by
    rw [← twoE_true, ← twoE_false]
    exact leviEmb_apply_ne k _ _ (by decide) _ _
  have h1 : ∀ i j : Fin r, h.val (Fin.castAdd t i) (Fin.castAdd t j) = (1 : Matrix (Fin r) (Fin r) k) i j :=
    fun i j => by
      rw [← twoE_false, ← twoE_false, hdef, leviEmb_apply_same, Pi.mulSingle_eq_of_ne (by decide)]
      rfl
  have hsub : h.val.submatrix (Fin.natAdd r) (Fin.natAdd r) = g.val := by
    ext i j
    rw [Matrix.submatrix_apply, ← twoE_true, ← twoE_true, hdef, leviEmb_apply_same, Pi.mulSingle_eq_same]
  exact hv h hKO (fun i j => by simp [h0]) (fun i j => by simp [h1, Matrix.one_apply])
    (Matrix.GeneralLinearGroup.det g) (by rw [hsub, Matrix.GeneralLinearGroup.val_det_apply])

theorem jacquet_ne_zero_of_isBlockVec_two : GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (r + t)) k) V) (v : V), IsSmooth π → π.IsIrreducible → IsTame χ → v ≠ 0 → IsBlockVec χ π v → (Submodule.Quotient.mk v : Jacquet π (unipRad k (two (stdSum (rfl : r + t = r + t))))) ≠ 0 ∧ ∀ g ∈ KO k (Fin t), jac (two (stdSum (rfl : r + t = r + t))) π (Pi.mulSingle true g) (Submodule.Quotient.mk v) = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • Submodule.Quotient.mk v := by
  intro hP k _ _ _ _ r t χ V _ _ π v hsm hirr hχ hv0 hv
  refine ⟨?_, ?_⟩
  · intro hx
    apply hv0
    have hx' : (Submodule.Quotient.mk v : Jacquet π (unipRad k (blocks2 r t))) = 0 := by
      rw [unipRad_blocks2]; exact hx
    refine hP k (r + t) 2 (sz r t) (blocks2 r t) ⟨V, π, hsm, hirr⟩ v ?_ hx'
    rw [unipRad_blocks2]
    rintro ⟨h, hh⟩
    have := sup_le (KOne_le_stab hχ hv) (unipRad_two_inf_KO_le_stab hv) hh
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    exact this
  · intro g hg
    rw [jac_mk, deltaHalf_mulSingle hg, act_mulSingle hv hg, inv_one, Units.val_one, one_smul,
      Submodule.Quotient.mk_smul]

end GlobalTheory.JacBlockTwo

end
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeviRepParabolicChar
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.EigenFactor

section Avg

variable {H W W' : Type} [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

end Avg

section Tensor

variable {β : Type} [Fintype β] [DecidableEq β] {Γ X : β → Type} [∀ j, Group (Γ j)] [∀ j, AddCommGroup (X j)]
  [∀ j, Module ℂ (X j)]

end Tensor

theorem exists_eig_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (β : Type) [Fintype β] [DecidableEq β] (m : β → Type) [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)] (X : β → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)] (ρ : ∀ j, Representation ℂ (GL (m j) k) (X j)) (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (Levi k m) Y) (a : β) (χ : kˣ →* ℂˣ) (y : Y), (∀ j, IsSmooth (ρ j)) → IsSmoothChar χ → IsSubquotient τ (piTensor ρ) → y ≠ 0 → (∀ g ∈ KO k (m a), τ (Pi.mulSingle a g) y = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • y) → ∃ z : X a, z ≠ 0 ∧ ∀ g ∈ KO k (m a), ρ a g z = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • z := by
  first
  | exact @_root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector
  | exact _root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector
  | (apply _root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector <;> assumption)
  | (intros; apply _root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector ..)

end GlobalTheory.EigenFactor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MultiProdHeadComp
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead
open scoped TensorProduct

namespace GlobalTheory.ProdReorder

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V₀ V₁ V₂ V₃ V₄ V₅ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃] [AddCommGroup V₄] [Module ℂ V₄]
  [AddCommGroup V₅] [Module ℂ V₅]

theorem ind₂_congr_right_prod {a b c N M : ℕ} (h : a + M = N) (h' : b + c = M)
    (ρ₀ : Representation ℂ (GL (Fin a) k) V₀) (ρ₁ : Representation ℂ (GL (Fin b) k) V₁)
    (ρ₂ : Representation ℂ (GL (Fin c) k) V₂) (μ : Representation ℂ (GL (Fin M) k) V₃)
    (φ : Nonempty (μ.Equiv (ind₂ (stdSum h') (extTensor ρ₁ ρ₂)))) :
    Nonempty ((ind₂ (stdSum h) (extTensor ρ₀ μ)).Equiv
      (ind₂ (stdSum h) (extTensor ρ₀ (ind₂ (stdSum h') (extTensor ρ₁ ρ₂))))) :=
  ind₂_congr h (eqv_refl ρ₀) φ

theorem ind₂_congr_left_prod {a b c N M : ℕ} (h : M + c = N) (h' : a + b = M)
    (ρ₁ : Representation ℂ (GL (Fin a) k) V₁) (ρ₂ : Representation ℂ (GL (Fin b) k) V₂)
    (ρ₃ : Representation ℂ (GL (Fin c) k) V₃) (μ : Representation ℂ (GL (Fin M) k) V₀)
    (φ : Nonempty (μ.Equiv (ind₂ (stdSum h') (extTensor ρ₁ ρ₂)))) :
    Nonempty ((ind₂ (stdSum h) (extTensor μ ρ₃)).Equiv
      (ind₂ (stdSum h) (extTensor (ind₂ (stdSum h') (extTensor ρ₁ ρ₂)) ρ₃))) :=
  ind₂_congr h φ (eqv_refl ρ₃)

theorem ind₂_congr_left_prod₂ {a b c d e N M : ℕ} (h : M + e = N) (h₁ : a + b = M) (h₂ : c + d = M)
    (ρ₁ : Representation ℂ (GL (Fin a) k) V₁) (ρ₂ : Representation ℂ (GL (Fin b) k) V₂)
    (ρ₃ : Representation ℂ (GL (Fin c) k) V₃) (ρ₄ : Representation ℂ (GL (Fin d) k) V₄)
    (ρ₅ : Representation ℂ (GL (Fin e) k) V₅)
    (φ : Nonempty ((ind₂ (stdSum h₁) (extTensor ρ₁ ρ₂)).Equiv (ind₂ (stdSum h₂) (extTensor ρ₃ ρ₄)))) :
    Nonempty ((ind₂ (stdSum h) (extTensor (ind₂ (stdSum h₁) (extTensor ρ₁ ρ₂)) ρ₅)).Equiv
      (ind₂ (stdSum h) (extTensor (ind₂ (stdSum h₂) (extTensor ρ₃ ρ₄)) ρ₅))) :=
  ind₂_congr h φ (eqv_refl ρ₅)

theorem multiProd_head_comp {s u : ℕ} {d : Fin s → ℕ} (σ : ∀ a, Irr k (d a)) (ι : Fin (u + 1) → Fin s)
    (a₀ : Fin s) (κ : Fin u → Fin s) (h0 : ι 0 = a₀) (hκ : ∀ i, ι i.succ = κ i) {T N : ℕ}
    (e : (Σ i, Fin (d (ι i))) ≃ Fin N) (h : d a₀ + T = N) (e' : (Σ i, Fin (d (κ i))) ≃ Fin T) :
    Nonempty ((multiProd e fun i => (σ (ι i)).π).Equiv
      (ind₂ (stdSum h) (extTensor (σ a₀).π (multiProd e' fun i => (σ (κ i)).π)))) := by
  subst h0
  have hk : (fun i => ι i.succ) = κ := funext hκ
  subst hk
  exact multiProd_head (fun i => (σ (ι i)).π) e h e'

end GlobalTheory.ProdReorder
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDet
section
noncomputable section

namespace GlobalTheory.RankOneComp

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField
  IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Char

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [_root_.NumberField.IsTotallyComplex E]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem locPar_ofChar_unr_iff (hL : GlobalTheory.Published.LocalLanglandsGL) (χ : HChar E) (h : IsPlaceOver A w) :
    (ParLaws.locPar hL (CG.ofChar χ) h).unr ↔ χ.UnrAt w := by
  obtain ⟨a, ha, ε, -, H⟩ := ParLaws.isRec_locRec hL h
  rw [ParLaws.locPar_ofChar, H.one, Test.unr_lpOfChar_iff ha (ParLaws.isSmoothChar_loc χ w)]
  refine forall_congr' fun x => imp_congr_left ?_
  have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
  rw [← ord_eq_zero_iff, SphCompletion.ord_completion, neg_eq_zero, IsUnitAt]
  constructor
  · intro hl
    rw [← WithZero.exp_log h0, hl, WithZero.exp_zero]
  · intro hv
    rw [hv, WithZero.log_one]

theorem locPar_ofChar_frob (hL : GlobalTheory.Published.LocalLanglandsGL) (χ : HChar E) (h : IsPlaceOver A w) (hu : χ.UnrAt w) :
    (ParLaws.locPar hL (CG.ofChar χ) h).frobEig = {(((χ.val w)⁻¹ : ℂˣ) : ℂ)} := by
  have e : χ.loc w = SmGL.unrChar (w.adicCompletion E) (χ.val w) := by
    refine MonoidHom.ext fun x => ?_
    have h2 := unif_spec w
    have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
    have h1 : IsUnitAt w (x * (atFin w (unif w) ^ ord (w.adicCompletion E) x)⁻¹) := by
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
        map_inv₀, map_zpow₀, h2, ← WithZero.exp_zsmul, SphCompletion.ord_completion]
      simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
      rw [WithZero.exp_log h0, mul_inv_cancel₀ h0]
    have h3 := hu _ h1
    rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3
    exact h3
  obtain ⟨a, ha, ε, -, H⟩ := ParLaws.isRec_locRec hL h
  have e2 : ParLaws.locPar hL (CG.ofChar χ) h = WD.mk (WDRep.diag h fun _ : Fin 1 => (χ.val w)⁻¹) := by
    rw [ParLaws.locPar_ofChar, H.one]
    have : ∀ (ξ : (w.adicCompletion E)ˣ →* ℂˣ) (hξ : WeilDeligne.IsSmooth (ξ.comp a)),
        ξ = SmGL.unrChar (w.adicCompletion E) (χ.val w) →
        WD.lpOfChar h (ξ.comp a) hξ = WD.mk (WDRep.diag h fun _ : Fin 1 => (χ.val w)⁻¹) := by
      rintro ξ hξ rfl
      exact Test.lpOfChar_unrChar ha _ _
    exact this _ _ e
  rw [e2, WD.frobEig_diag]
  simp

end Char

end GlobalTheory.RankOneComp

end
end

