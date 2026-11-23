module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
public import Formalism.LocalRingCardinality.SpanPowerMembership.PlacesOverNcardOfSplitInj
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationLeOneOfMemZmu
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastTwoStepsGuarded
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitarySphericalSatakeMultisetMapInv

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LabelSettingTameGenerator
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne Formalism.CyclotomicNorms

namespace GlobalTheory.LabLaws

section WDLaws

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}
variable {g : ℕ} [Fact g.Prime]

end WDLaws

section Comparison₂

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

def LabTie (T : GlobalTheory.RowTie.WDTie N A) (τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ)
    (γ : Fin 2 → PlE H → G H.E N.Om) : Prop :=
  ∀ (k : Fin 2) (v : N.PlG k),
    haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    IsTeich (τ k) ∧ TameGenAt (N.plOm.1 (A.plGw k v)) (γ k (A.plGw k v)) ∧
      ∀ a : A.LP (A.plGw k v), A.items₂ k (A.plGw k v) a = WD.lab (τ k) (γ k (A.plGw k v)) (T.e _ a)

theorem tieLab_of_labTie {T : GlobalTheory.RowTie.WDTie N A} {τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ}
    {γ : Fin 2 → PlE H → G H.E N.Om} (hT : LabTie T τ γ) : GlobalTheory.RowCopy.TieLab N A := by
  refine ⟨fun k v a s => ?_, fun k v a => ?_⟩
  · haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    rw [(hT k v).2.2, (hT k v).2.2, T.tw, WD.lab_lpTw]
  · haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    rw [(hT k v).2.2, ← T.dim]
    exact WD.natDegree_lab_le _ _ _

end Comparison₂

section Inhabited

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

end Inhabited

end GlobalTheory.LabLaws
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDataIntegralAwayFromLevels
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory.CplTwoInt

open GlobalTheory.GO.ChRoot (mem_stdAt' intAt_natCast intAt_one' intAt_zero' psi_root)

theorem intOff_prod {S : Finset ℕ} {ι : Type} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, IntOff S (f i)) :
    IntOff S (∏ i ∈ s, f i) :=
  Finset.prod_induction f (IntOff S) (fun _ _ ha hb => ha.mul hb) IntOff.one h

theorem sNum_pow {S : Finset ℕ} {a : ℕ} (h : SNum S a) (k : ℕ) : SNum S (a ^ k) :=
  ⟨pow_pos h.1 k, fun q hq hd => h.2 q hq (hq.dvd_of_dvd_pow hd)⟩

section Lin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem intAt_eval {n : ℕ} (η : Sp E n →ₗ[E] E) (c a : E) (y : Sp E n)
    (hη : ∀ i, IntAt P (c * η (Pi.single i 1))) (hy : a • y ∈ stdAt E n P) : IntAt P (a * c * η y) := by
  have hy' := mem_stdAt'.1 hy
  have e : η y = ∑ i, y i * η (Pi.single i 1) := by
    conv_lhs => rw [← Finset.univ_sum_single y]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (Pi.single i (y i) : Sp E n) = y i • Pi.single i (1 : E) by
      ext j; by_cases h : j = i <;> simp [h, Pi.single_apply], map_smul, smul_eq_mul]
  rw [e, Finset.mul_sum]
  refine Finset.sum_induction _ (IntAt P) (fun _ _ ha hb => ha.add hb) intAt_zero' fun i _ => ?_
  have := (hy' i).mul (hη i)
  simp only [Pi.smul_apply, smul_eq_mul] at this
  convert this using 1
  ring

theorem smul_symm_mem {n : ℕ} {N : Submodule (𝓞 E) (Sp E n)} {f : Sp E n ≃ₗ[E] Sp E n}
    (hf : ∀ x, f x ∈ localization₂ P.asIdeal N ↔ x ∈ stdAt E n P) (a : E) {z : Sp E n} (hz : a • z ∈ localization₂ P.asIdeal N) :
    a • f.symm z ∈ stdAt E n P := by
  rw [← hf, map_smul, LinearEquiv.apply_symm_apply]
  exact hz

end Lin

section Yb

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem repY_mem {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} {Yb : Set (Sp X.E n)} (hY : Yb ∈ ybSet sel mu cst N)
    (P : rowSG Pr sel mu) :
    ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else cst.M)) • repY Yb ∈ localization₂ P.1.asIdeal N := by
  obtain ⟨y, hy, rfl⟩ := hY
  have hq : (qOf P.1 : X.E) ≠ 0 := by exact_mod_cast (GlobalTheory.GO.ChRoot.qOf_pos P.1).ne'
  have hs : ∀ (k : ℕ) v, v ∈ localization₂ P.1.asIdeal N → ((qOf P.1 : X.E) ^ k) • v ∈ localization₂ P.1.asIdeal N := by
    intro k v hv
    have := Submodule.smul_mem _ ((qOf P.1 : 𝓞 X.E) ^ k) hv
    rwa [← algebraMap_smul X.E, map_pow, map_natCast] at this
  have key : ∀ z, z - y ∈ locLat (rowSG Pr sel mu) N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) →
      ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else cst.M)) • z ∈ localization₂ P.1.asIdeal N := by
    intro z hz
    rw [mem_locLat] at hy hz
    have h1 := hy P
    have h2 := hz P
    rw [show z = y + (z - y) by abel, smul_add]
    split_ifs at h1 h2 ⊢ with hP
    · refine add_mem ?_ ?_
      · simpa using h1
      · exact hs 1 _ (by simpa using h2)
    · refine add_mem ?_ ?_
      · simpa [zpow_neg] using h1
      · have e : ((qOf P.1 : X.E) ^ cst.M) • (z - y) =
            ((qOf P.1 : X.E) ^ (cst.M + cst.M)) • (((qOf P.1 : X.E) ^ (cst.M : ℤ))⁻¹ • (z - y)) := by
          rw [smul_smul, zpow_natCast, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), mul_one]
        rw [e]
        exact hs _ _ h2
  exact key _ (Classical.epsilon_spec (p := fun z => z - y ∈ locLat (rowSG Pr sel mu) N
    (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))) ⟨y, by simp⟩)

end Yb

end GlobalTheory.CplTwoInt

namespace GlobalTheory.CplTwoInt

open GlobalTheory.GO.ChRoot (mem_stdAt' intAt_natCast intAt_one' intAt_zero' psi_root)

section Ft

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem ftY_intOff (hc : cst.Ok) (P : rowSG Pr sel mu) (hG : P.1 ∈ Pr.vGs → cst.D P = 1)
    (hQ : P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) (σ : X.K →+* ℂ) {B : Finset ℕ} (hB : SNum B (qOf P.1)) {n : ℕ}
    (η : Sp X.E n →ₗ[X.E] X.E) {y : Sp X.E n}
    (hy : ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else cst.M)) • y ∈ stdAt X.E n P.1) :
    IntOff B (σ (ftY sel mu cst P η y)) := by
  have he : IntAt P.1 ((epsSg : ℤ) : X.E) := by simpa [epsSg] using IntAt.coe P.1 (-1 : 𝓞 X.E)
  have hpos : 0 < qOf P.1 ^ cst.D P := pow_pos (GlobalTheory.GO.ChRoot.qOf_pos P.1) _
  unfold ftY
  by_cases hP : P.1 ∈ Pr.vGs
  · rw [if_pos hP] at hy ⊢
    split_ifs with hη
    · refine IntOff.of_pow hpos ?_
      rw [← map_pow, psi_root hc P _ ?_, map_one]
      rw [hG hP, pow_one]
      have h1 := intAt_eval η 1 _ y (fun i => by simpa using hη i) hy
      convert he.mul h1 using 1
      ring
    · simpa using (IntOff.zero : IntOff B 0)
  · rw [if_neg hP] at hy ⊢
    split_ifs with hη
    · rw [map_mul, map_inv₀, map_pow, map_natCast]
      refine IntOff.mul ?_ (IntOff.of_pow hpos ?_)
      · simpa [Nat.cast_pow] using IntOff.inv_nat (sNum_pow hB (cst.M * n))
      · rw [← map_pow, psi_root hc P _ ?_, map_one]
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (hQ hP)
        have h1 := intAt_eval η _ _ y hη hy
        have hk' : IntAt P.1 ((qOf P.1 : X.E) ^ k) := by simpa using intAt_natCast (P := P.1) (qOf P.1 ^ k)
        rw [hk]
        convert (he.mul hk').mul h1 using 1
        ring
    · simpa using (IntOff.zero : IntOff B 0)

end Ft

theorem xiCpl2_intOff (hPhi : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D)
      (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ
      (P : HeightOneSpectrum (𝓞 t.X.E)) x,
      IntOff (t.O u μ).S (t.seam.σ₀ (PhiTop (R := D.R) t.Ch (t.tup μ) (t.cst μ).sharp t.m2 P x))) :
    ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ p Yb d x, Yb ∈ ybSet t.sel (t.tup μ) (t.cst μ) p.deco.1.N → IntOff (t.O u μ).S (t.seam.σ₀ (XiCpl2 (R := D.R) (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) t.m2 p Yb d x)) := by
  intro D L hT Gi Gl K Y cX ex t u μ p Yb d x hY
  have hok := t.idx_ok μ
  unfold XiCpl2
  rw [map_mul, map_prod]
  refine IntOff.mul ?_ (intOff_prod _ _ fun P _ => ?_)
  · unfold phiT
    split_ifs
    · simpa using (IntOff.one : IntOff (t.O u μ).S 1)
    · simpa using (IntOff.zero : IntOff (t.O u μ).S 0)
  · rw [map_mul]
    refine IntOff.mul (hPhi D L hT Gi Gl K Y cX ex t u μ P.1 _) ?_
    exact ftY_intOff t.sel (t.tup μ) (t.cst μ) hok.cst_ok P (hok.depthG P) (hok.depthQ P) _
      (GlobalTheory.KerTie.sNum_qOf_rowSG D L hT Gi Gl K Y cX ex t u μ P) _
      (smul_symm_mem (GlobalTheory.ColPeriod.isFrames_frsF p P) _ (repY_mem t.sel (t.tup μ) (t.cst μ) hY P))

theorem xiCpl2_intOff_tied : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ p Yb d x, Yb ∈ ybSet t.sel (t.tup μ) (t.cst μ) p.deco.1.N → IntOff (t.O u μ).S (t.seam.σ₀ (XiCpl2 (R := D.R) (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) t.m2 p Yb d x)) :=
  xiCpl2_intOff fun D L hT Gi Gl K Y cX ex t u μ P x => (GlobalTheory.T.chain_local_data_integral_off_levels D L hT Gi Gl K Y cX ex t u μ P).2 x

end GlobalTheory.CplTwoInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotDvdCardStabFrm
section
noncomputable section

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain _root_.Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator (FnModAt FnMod facTop facPen Zmu)
open GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance (DegOneUnram)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver IsFrames)
open GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable (jetSum RatIdx)
open GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint (WtCompat InDeg HAt LatWithBasis)

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K))

def Bd {V V' : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V']
    (c : K) (M : Submodule (𝓞 K) V) (M' : Submodule (𝓞 K) V') (k : V →ₗ[K] V') : Prop :=
  ∀ v ∈ localization₂ w.asIdeal M, c • k v ∈ localization₂ w.asIdeal M'

def WtUnit (S : GSD K) : Prop := ∀ d : S.D, w.valuation K ((Nat.card (MulAction.stabilizer S.G d) : ℕ) : K)⁻¹ ≤ 1

variable {w}

theorem Bd.transfer {S S' : GSD K} (g : S.G) (g' : S'.G) {M M₂ : Submodule (𝓞 K) S.V} {M' M₂' : Submodule (𝓞 K) S'.V}
    (hM : M₂ = M.map ((S.ρ g).restrictScalars (𝓞 K))) (hM' : M₂' = M'.map ((S'.ρ g').restrictScalars (𝓞 K)))
    {k k₂ : S.V →ₗ[K] S'.V} (hk : k₂ = (S'.ρ g') ∘ₗ k ∘ₗ (S.ρ g⁻¹)) {c : K} (h : Bd w c M₂ M₂' k₂) : Bd w c M M' k := by
  subst hM hM' hk
  rintro v ⟨s, hs, hv⟩
  obtain ⟨t, ht, y, hy, e⟩ := h (S.ρ g v) ⟨s, hs, s • v, hv, by simp⟩
  refine ⟨t, ht, ?_⟩
  have e1 : S.ρ g⁻¹ (S.ρ g v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have e2 : y = t • c • k v := by
    have h2 := congrArg (S'.ρ g'⁻¹) e
    simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, e1, LinearMap.map_smul_of_tower, map_smul] at h2
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at h2
    exact h2
  exact e2 ▸ hy

theorem opOf_bound {S S' : GSD K} (A : ClsKer S S') (h : S.Ok) (s : S.Sec) (hw : WtUnit w S) {c : K}
    (hk : ∀ d d', Bd w c (S.Del d) (S'.Del d') (A.k d d')) {c₀ : K} (φ : S.EqFun)
    (hφ : ∀ d, c₀ • φ.1 d ∈ localization₂ w.asIdeal (S.Del d)) (d' : S'.D) :
    (c * c₀) • (A.opOf h s φ).1 d' ∈ localization₂ w.asIdeal (S'.Del d') := by
  change (c * c₀) • A.appOf h s φ d' ∈ _
  unfold ClsKer.appOf
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun x _ => ?_
  rw [smul_comm, wt_eq_card]
  refine smul_mem_localizationAt_of_le w _ (hw _) ?_
  rw [mul_smul, ← map_smul]
  exact hk _ _ _ (hφ _)

theorem comp_bound {S₀ S S₁ : GSD K} {Y : Cpl S} (A : CplKer S₀ S S₁ Y) (h : S.Ok) (s : S.Sec) (hw : WtUnit w S) {c₁ c₂ : K}
    (h1 : ∀ d₀ d, ∀ y ∈ Y.ys d, Bd w c₁ (S₀.Del d₀) (S.Del d) (A.k1 d₀ d y))
    (h2 : ∀ d d₁, ∀ y ∈ Y.ys d, Bd w c₂ (S.Del d) (S₁.Del d₁) (A.k2 d y d₁)) (d₀ : S₀.D) (d₁ : S₁.D) :
    Bd w (c₂ * c₁) (S₀.Del d₀) (S₁.Del d₁) ((A.comp h s).k d₀ d₁) := by
  intro v hv
  simp only [CplKer.comp, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun x _ => ?_
  rw [smul_comm, wt_eq_card]
  refine smul_mem_localizationAt_of_le w _ (hw _) ?_
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun y hy => ?_
  have hy' : y ∈ Y.ys (s.rep x) := by simpa using hy
  rw [mul_smul, ← map_smul]
  exact h2 _ _ y hy' _ (h1 _ _ y hy' v hv)

theorem colTo_bound {F : ℕ → GFam K} (kk : KerFam F) (hF : ∀ j, (F j).Ok) (c : ℕ → K)
    (φ : (F 0).Forms) (hφ : ∀ b d, (φ b).1 d ∈ localization₂ w.asIdeal (((F 0).mem b).Del d)) (n : ℕ)
    (hw : ∀ j < n, ∀ b, WtUnit w ((F j).mem b))
    (hk : ∀ j < n, ∀ al be d d', Bd w (c j) (((F j).mem al).Del d) (((F (j + 1)).mem be).Del d') ((kk j al be).k d d'))
    (b : (F n).β) (d : ((F n).mem b).D) :
    (∏ j ∈ Finset.range n, c j) • (kk.colTo hF n φ b).1 d ∈ localization₂ w.asIdeal (((F n).mem b).Del d) := by
  induction n with
  | zero => rw [Finset.prod_range_zero, one_smul]; exact hφ b d
  | succ n ih =>
    have e : (kk.colTo hF (n + 1) φ b).1 d =
        ∑ al, ((kk n al b).opOf (hF n al) ((F n).mem al).outSec (kk.colTo hF n φ al)).1 d := by
      change (KerFam.step kk hF n (kk.colTo hF n φ) b).1 d = _
      simp only [KerFam.step, GFam.Mat.opOf, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply,
        LinearMap.proj_apply, Submodule.coe_sum, Finset.sum_apply]
    rw [e, Finset.smul_sum, Finset.prod_range_succ, mul_comm]
    exact Submodule.sum_mem _ fun al _ => opOf_bound _ _ _ (hw n (Nat.lt_succ_self n) al) (hk n (Nat.lt_succ_self n) al b) _
      (ih (fun j hj => hw j (Nat.lt_succ_of_lt hj)) (fun j hj => hk j (Nat.lt_succ_of_lt hj)) al) d

theorem colCpl_bound {F : ℕ → GFam K} (kk : KerFam F) (hF : ∀ j, (F j).Ok) {n : ℕ} (hw : ∀ j ≤ n, ∀ b, WtUnit w ((F j).mem b))
    (c : ℕ → K) {S S₁ : GSD K} {Y : Cpl S} (A : ∀ b : (F n).β, CplKer ((F n).mem b) S S₁ Y) (h : S.Ok) (hS : WtUnit w S)
    (hk : ∀ j < n, ∀ al be d d', Bd w (c j) (((F j).mem al).Del d) (((F (j + 1)).mem be).Del d') ((kk j al be).k d d'))
    (h1 : ∀ b d₀ d, ∀ y ∈ Y.ys d, Bd w (c n) (((F n).mem b).Del d₀) (S.Del d) ((A b).k1 d₀ d y))
    (h2 : ∀ b d d₁, ∀ y ∈ Y.ys d, Bd w (c (n + 1)) (S.Del d) (S₁.Del d₁) ((A b).k2 d y d₁))
    (φ : (F 0).Forms) (hφ : ∀ b d, (φ b).1 d ∈ localization₂ w.asIdeal (((F 0).mem b).Del d)) (d : S₁.D) :
    (∏ j ∈ Finset.range (n + 2), c j) • (colCpl kk hF n A h φ).1 d ∈ localization₂ w.asIdeal (S₁.Del d) := by
  have e : (colCpl kk hF n A h φ).1 d =
      ∑ b, (((A b).comp h S.outSec).opOf (hF n b) ((F n).mem b).outSec (kk.colTo hF n φ b)).1 d := by
    simp only [colCpl, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, Submodule.coe_sum, Finset.sum_apply]
  have e2 : ∏ j ∈ Finset.range (n + 2), c j = (c (n + 1) * c n) * ∏ j ∈ Finset.range n, c j := by
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    ring
  rw [e, Finset.smul_sum, e2]
  exact Submodule.sum_mem _ fun b _ => opOf_bound _ _ _ (hw n le_rfl b) (comp_bound (A b) h _ hS (h1 b) (h2 b)) _
    (colTo_bound kk hF c φ hφ n (fun j hj => hw j hj.le) hk b) d

end Generic

theorem not_dvd_card_stab_frm {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}
    (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (d : DecoF X.E n ST SG Q)
    [Finite (MulAction.stabilizer (FrmG Λ Θ) d)] {p : ℕ} (hp : p.Prime) (hb : Module.finrank ℚ X.E * n + 1 < p) :
    ¬ p ∣ Nat.card (MulAction.stabilizer (FrmG Λ Θ) d) := by
  refine not_dvd_card_of_injective (((UF X.E n).subtype.comp (MonoidHom.fst _ _)).comp (Subgroup.subtype _)) ?_ hp hb
  rw [injective_iff_map_eq_one]
  rintro ⟨⟨γ, h, c⟩, hs⟩ h1
  have h2 : γ = 1 := Subtype.ext h1
  subst h2
  have h3 : h.1 = 1 := glg_eq_one_of_fix d.1.1 h.1 (congrArg (fun x : DecoF X.E n ST SG Q => x.1.1.1) hs)
  have h4 : c.1 = 1 := by
    funext P
    have h5 : (1 : Sp X.E n ≃ₗ[X.E] Sp X.E n) * d.1.2 P * ((c.1 P)⁻¹).1 = d.1.2 P :=
      congrArg (fun x : DecoF X.E n ST SG Q => x.1.2 P) hs
    rw [one_mul, mul_eq_left] at h5
    exact inv_eq_one.1 (Subtype.ext h5)
  exact Subtype.ext (Prod.ext rfl (Prod.ext (Subtype.ext h3) (Subtype.ext h4)))

theorem stdOver_tilH {E : Type} [Field E] [NumberField E] [StarRing E] {N n : ℕ} (hN : N = n + 1)
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {pi : 𝓞 E} (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ v : SG, pi ∉ v.1.asIdeal)
    (d : DecoSet (E := E) (n := n) (ST := ∅) (SG := SG)) {p : ℕ} (h : StdOver p d.1.N) : StdOver p (DecoSet.tilH (ST := ST) hN pi d).1.N := by
  subst hN
  change StdOver p (DecoSet.til (ST := ST) pi d).1.N
  rw [DecoSet.til_val d hT hG]
  intro P hP
  ext x
  change x ∈ localization₂ P.asIdeal (tilN d.1.N) ↔ _
  rw [mem_localization_tilN, h P hP, GlobalTheory.TopStep.mem_stdAt, GlobalTheory.TopStep.mem_stdAt, Fin.forall_fin_succ']
  rfl

section Column

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (A : Amb X)

theorem exists_std_pt (hM : StdMove) (hPr : Pr.Ok) (i : Fin 2) (u : Pr.Word) (j : ℕ) (b : L.β j)
    (p : ((chF W sel mu L u j).mem b).D) : ∃ g : ((chF W sel mu L u j).mem b).G, StdOver (Pr.g i) (DecoF.deco (g • p)).1.N := by
  obtain ⟨γ, hγ⟩ := hM X Pr hPr i _ (DecoF.deco p).1.N ⟨(DecoF.deco p).2.lat, (DecoF.deco p).2.uni⟩
  exact ⟨(γ, 1, 1), hγ⟩

theorem evGSD_del_smul (hPr : Pr.Ok) (hsel : IsSel X sel) (u : Pr.Word) (hS : Pr.T u ∈ S) (P : LevFam X.E X.K R.r Pr.vGs)
    (γ : UF X.E (R.N R.m - 1)) (d : (evGSD W Ch sel mu P u).D) :
    (evGSD W Ch sel mu P u).Del (((γ, 1) : (evGSD W Ch sel mu P u).G) • d) =
      ((evGSD W Ch sel mu P u).Del d).map (((evGSD W Ch sel mu P u).ρ (γ, 1)).restrictScalars (𝓞 X.K)) := by
  have h1 := DecoSet.tilH_smul (ST := Pr.vT u) (N_m_succ R) (γ, (1 : GLG (E := X.E) (n := _) (SG := rowSG Pr sel mu))) d (conj_piT_notMem hPr u)
    (piT_notMem_rowSG sel mu hPr hsel u hS)
  have h2 : (evGSD W Ch sel mu P u).ρ (γ, 1) = (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).rho (extUH (N_m_succ R) γ) := by
    change ((((rowTy Ch sel mu P).inv.chr 1)⁻¹ : X.Kˣ) : X.K) •
      (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).rho (extUH (N_m_succ R) γ) = _
    rw [map_one, inv_one, Units.val_one, one_smul]
  rw [h2]
  refine Eq.trans ?_ (colVal_del_smul W u R.m (extUH (N_m_succ R) γ, extGH (N_m_succ R) 1) (tilQ sel mu u d))
  exact congrArg (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).Del h1

theorem wtUnit_chF (hX : X.Ok) (u : Pr.Word) (hF : ∀ j, (chF W sel mu L u j).Ok) {p : ℕ} (hp : p.Prime)
    (hb : 2 * X.f * R.N R.m + 1 < p) (w : HeightOneSpectrum (𝓞 X.K)) (hw : ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal) {j : ℕ} (hj : j ≤ R.m)
    (b : L.β j) : WtUnit w ((chF W sel mu L u j).mem b) := by
  intro d
  have hE : Module.finrank ℚ X.E = 2 * X.f := by
    rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, ← hX.card_Tau, mul_comm]
    rfl
  have := (hF j b).fin_stab d
  have hN : R.N j ≤ R.N R.m := Examples₂.N_mono hj
  exact (valuation_inv_natCast w hp hw (not_dvd_card_stab_frm (L.levG j b) (L.levQ j b) d hp
    (lt_of_le_of_lt (by rw [hE]; gcongr) hb))).le

end Column

end GlobalTheory.ColPeriod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceCompletionLeMaxUnramifiedAway2qd
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory

theorem bridge_field_le_unramified : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
    {N : NData R H what₂} (nbr : Br.NBr N) (i : N.Loc) (w : HeightOneSpectrum (𝓞 H.E))
    (hw : w ∈ placesOver H.E (N.l i)),
    N.l i ∉ H.small → N.l i ≠ H.q → N.l i ≠ H.d → (nbr i w hw).Kw.1 ≤ Loc.MaximalUnramifiedExtension (N.l i) := by
  intro R H what₂ N nbr i w hw h2 hq hd
  have hK := _root_.GlobalTheory.padicAlgCl_finite_dense_eq_adjoin (N.l i) H.E ((nbr i w hw).j.comp (algebraMap H.E N.Om)) (nbr i w hw).Kw.1
    (nbr i w hw).j_E (nbr i w hw).Kw.2 (nbr i w hw).j_dense
  rw [hK, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, rfl⟩
  exact _root_.GlobalTheory.HostKur.host_image_mem_Kur H (N.l i) h2 hq hd _ x

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarySphericalComponentOfReading
section
noncomputable section

namespace GlobalTheory.SplitRead

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL
  GlobalTheory.SplitWeil GlobalTheory.RowTie

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end GlobalTheory.SplitRead
end
end

