module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0851
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0191
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0379
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0210
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1189

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.InePolCoeffZero
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N Formalism.L2.Host Module
open _root_.GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.HeightCounting GlobalTheory.SmGL GlobalTheory.SatakeFlip GlobalTheory.LocGL
open GlobalTheory.Mem.Chr hiding HChar

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalS

section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

def SepW (y : WD h) : Prop := y.tame ∧ ∃ s ∈ Ine (F := E) B, (y.inePol s).Separable

theorem SepW.ncW {y : WD h} (k : SepW y) (ht : thr w y.lpDim = 2) : NcW y := by
  obtain ⟨k1, s, hs, k2⟩ := k
  refine ⟨(WD.tame_iff_inePol y).1 k1, WD.noMonodromy_of_inertia_separable_charpoly E Ω B w h y s hs k2, fun γ hγ hc z hz => ?_⟩
  exfalso
  obtain ⟨n, a, rfl⟩ := y.exists_rep
  rw [WD.tame_mk] at k1
  rw [ht, WD.inePol_of_mem_Ine _ hγ, WD.charPol_mk] at hz
  rw [WD.inePol_of_mem_Ine _ hs, WD.charPol_mk] at k2
  let U := End.eigenspace (a.ρ (ineIncl h ⟨γ, hγ⟩)) z
  let K : Subgroup (Ine (F := E) B) :=
    { carrier := {σ | ∃ c : ℂ, ∀ v ∈ U, a.ρ (ineIncl h σ) v = c • v}
      one_mem' := ⟨1, fun v _ => by simp⟩
      mul_mem' := fun {x y} ⟨c, hc⟩ ⟨d, hd⟩ => ⟨d * c, fun v hv => by
        rw [map_mul, map_mul, End.mul_apply, hd v hv, map_smul, hc v hv, smul_smul]⟩
      inv_mem' := fun {x} ⟨c, hc⟩ => ⟨c⁻¹, fun v hv => by
        have e : a.ρ (ineIncl h x⁻¹) (a.ρ (ineIncl h x) v) = v := by
          rw [← End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, End.one_apply]
        rw [hc v hv, map_smul] at e
        by_cases h0 : c = 0
        · rw [h0, zero_smul] at e; rw [← e]; simp
        · rw [← e, smul_smul, inv_mul_cancel₀ h0, one_smul, e]⟩ }
  have hop : IsOpen (K : Set (Ine (F := E) B)) :=
    K.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (IsOpen.mem_nhds a.smooth (by
      show a.ρ (ineIncl h 1) = 1
      rw [map_one, map_one])) fun σ hσ => ⟨1, fun v _ => by
      have : a.ρ (ineIncl h σ) = 1 := hσ
      rw [this]; simp⟩)
  have hK : IsClosed ((K.map (Ine (F := E) B).subtype : Subgroup (G E Ω)) : Set (G E Ω)) :=
    (isClosed_Ine B).isClosedEmbedding_subtypeVal.isClosedMap _ (K.isClosed_of_isOpen hop)
  have hle : Subgroup.closure (insert γ (Wild E B : Set (G E Ω))) ≤ K.map (Ine (F := E) B).subtype := by
    rw [Subgroup.closure_le]
    rintro u (rfl | hu)
    · exact ⟨⟨u, hγ⟩, ⟨z, fun v hv => End.mem_eigenspace_iff.1 hv⟩, rfl⟩
    · exact ⟨⟨u, Wild_le_Ine hu⟩, ⟨1, fun v _ => by rw [k1 _ hu]; simp⟩, rfl⟩
  obtain ⟨u, ⟨c, hu⟩, e⟩ := closure_minimal (SetLike.coe_subset_coe.mpr hle) hK (hc hs)
  obtain rfl : u = ⟨s, hs⟩ := Subtype.ext e
  have h1 : finrank ℂ U = (a.ρ (ineIncl h ⟨γ, hγ⟩)).charpoly.rootMultiplicity z := by
    rw [← LinearMap.finrank_maxGenEigenspace_eq, (a.semisimple _).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace]
  have h2 : finrank ℂ U ≤ (a.ρ (ineIncl h ⟨s, hs⟩)).charpoly.rootMultiplicity c := by
    rw [← LinearMap.finrank_maxGenEigenspace_eq, (a.semisimple _).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace]
    exact Submodule.finrank_mono fun v hv => End.mem_eigenspace_iff.2 (hu v hv)
  have h3 := rootMultiplicity_le_one_of_separable k2 c
  omega

theorem SepW.dual {y : WD h} (k : SepW y) : SepW y.lpDual := by
  obtain ⟨k1, s, hs, k2⟩ := k
  obtain ⟨n, a, rfl⟩ := y.exists_rep
  rw [WD.tame_mk] at k1
  refine ⟨?_, s⁻¹, inv_mem hs, ?_⟩
  · rw [WD.lpDual_mk, WD.tame_mk]
    intro σ hσ
    rw [WDRep.dual_ρ, k1 σ⁻¹ (inv_mem hσ)]
    rfl
  · rw [WD.inePol_of_mem_Ine _ hs, WD.charPol_mk] at k2
    rw [WD.lpDual_mk, WD.inePol_of_mem_Ine _ (inv_mem hs), WD.charPol_mk, WDRep.dual_ρ, LabDual.charpoly_dualMap]
    convert k2 using 3
    exact Subtype.ext (inv_inv s)

theorem SepW.transport {B' : ValuationSubring Ω} {w' : HeightOneSpectrum (𝓞 E)} {h' : IsPlaceOver B' w'} {n : ℕ}
    (c : Ω ≃+* Ω) (τ : E ≃+* E) (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x)) (hc : ∀ y, y ∈ B' ↔ c y ∈ B)
    {b' : WDRep h' (Fin n → ℂ)} {b : WDRep h (Fin n → ℂ)}
    (e : ∀ (σ' : Weil h') (σ : Weil h), (∀ z, c ((σ' : G E Ω) z) = (σ : G E Ω) (c z)) → b'.ρ σ' = b.ρ σ)
    (k : SepW (WD.mk b)) : SepW (WD.mk b') := by
  obtain ⟨k1, s, hs, k2⟩ := k
  rw [WD.tame_mk] at k1
  have hc' : ∀ y, y ∈ B ↔ c.symm y ∈ B' := fun y => by rw [hc, c.apply_symm_apply]
  have hs' := ConjTransport.conjG_mem_Ine c.symm τ.symm (ConjTransport.symm_alg c τ hτ) hc' hs
  refine ⟨(WD.tame_mk _).2 fun σ hσ => ?_, _, hs', ?_⟩
  · have hw : ConjTransport.conjG c τ hτ σ ∈ Wild E B := ConjTransport.conjG_mem_wild c τ hτ hc hσ
    rw [e σ (ineIncl h ⟨_, Wild_le_Ine hw⟩) fun z => (ConjTransport.conjG_apply_c c τ hτ _ z).symm]
    exact k1 _ hw
  · rw [WD.inePol_of_mem_Ine _ hs, WD.charPol_mk] at k2
    rw [WD.inePol_of_mem_Ine _ hs', WD.charPol_mk, e _ (ineIncl h ⟨s, hs⟩) fun z => c.apply_symm_apply _]
    exact k2
end

section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def Sep {w : PlE H} (y : A.LP w) : Prop := Tm N A y ∧ ∃ s ∈ Ine (F := H.E) (N.plOm.1 w), (A.inePol y s).Separable

variable {N A}

theorem tm_iff (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} (y : A.LP w) : Tm N A y ↔ (T.e w y).tame := by
  rw [WD.tame_iff_inePol]
  refine ⟨fun k σ hσ => ?_, fun k σ hσ hw => ?_⟩
  · rw [← T.inePol w y σ (Wild_le_Ine hσ), T.dim]
    exact k σ (Wild_le_Ine hσ) hσ
  · rw [T.inePol w y σ hσ, ← T.dim]
    exact k σ hw

theorem sep_iff (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} (y : A.LP w) : Sep N A y ↔ SepW (T.e w y) :=
  and_congr (tm_iff T y) (exists_congr fun s => and_congr_right fun hs => by rw [T.inePol w y s hs])

theorem nc_of_sep (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} {y : A.LP w} (ht : thr w (A.lpDim y) = 2) (h : Sep N A y) :
    Nc N A y :=
  (nc_iff T y).2 (((sep_iff T y).1 h).ncW (by rwa [T.dim]))

theorem sep_char (hLP : Formalism.MainNotions.SumRepresentations.At.TieLP N A) {w : PlE H} {y c : A.LP w} (hc : A.lpDim c = 1) (tc : Tm N A c)
    (h0 : ∀ s ∈ Ine (F := H.E) (N.plOm.1 w), (A.inePol c s).coeff 0 ≠ 0) (h : Sep N A y) : Sep N A (A.lpChar y c) := by
  obtain ⟨k1, s, hs, k2⟩ := h
  refine ⟨fun σ hσ hw => ?_, s, hs, ?_⟩
  · have e : A.inePol c σ = X - C 1 := by rw [tc σ hσ hw, hc]; simp
    rw [((hLP w y y c c 0 hc hc).2.2.2.2.2 σ hσ).2 1 e, scaleRoots_one, k1 σ hσ hw, A.lpDim_char _ _ hc]
  · obtain ⟨m1, m2⟩ := inePol_monic hLP c s hs
    rw [hc] at m2
    have e : A.inePol c s = X - C (-(A.inePol c s).coeff 0) := by
      rw [C_neg, sub_neg_eq_add]; exact m1.eq_X_add_C m2
    have hz : -(A.inePol c s).coeff 0 ≠ 0 := neg_ne_zero.2 (h0 s hs)
    rw [((hLP w y y c c 0 hc hc).2.2.2.2.2 s hs).2 _ e]
    obtain ⟨n1, -⟩ := inePol_monic hLP y s hs
    have sp := IsAlgClosed.splits (A.inePol y s)
    refine (nodup_roots_iff_of_splits ((monic_scaleRoots_iff _).2 n1).ne_zero (IsAlgClosed.splits _)).1 ?_
    rw [roots_scaleRoots _ hz.isUnit]
    exact (nodup_roots k2).map (mul_right_injective₀ hz)
end

theorem inePol_coeff_zero {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
    (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} (c : A.LP w) (s) (hs : s ∈ Ine (F := H.E) (N.plOm.1 w)) :
    (A.inePol c s).coeff 0 ≠ 0 := by
  rw [T.inePol w c s hs, WD.inePol_of_mem_Ine _ hs]
  obtain ⟨n, a, e⟩ := (T.e w c).exists_rep
  rw [← e, WD.charPol_mk]
  intro h0
  have hu : IsUnit (a.ρ (ineIncl (N.plOm.2 w) ⟨s, hs⟩)) := (Group.isUnit _).map a.ρ
  have hd := (LinearMap.isUnit_iff_isUnit_det _).1 hu
  rw [LinearMap.det_eq_sign_charpoly_coeff, h0, mul_zero] at hd
  exact not_isUnit_zero hd

end UpperTheory.GalS
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.PowEqOneOfRoots
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial Module
open _root_.GlobalTheory GlobalTheory.WeilDeligne
open scoped commutatorElement

namespace UpperTheory.GalS

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem mem_of_gen {n : ℕ} {a : WDRep h (Fin n → ℂ)} (ha : a.Tame) {γ : G E Ω} (hγ : TameGenAt A γ)
    (S : Subgroup (End ℂ (Fin n → ℂ))ˣ) (h1 : a.ρ.toHomUnits (ineIncl h ⟨γ, hγ.1⟩) ∈ S) (σ : Ine (F := E) A) :
    a.ρ.toHomUnits (ineIncl h σ) ∈ S := by
  let K : Subgroup (Ine (F := E) A) := S.comap (a.ρ.toHomUnits.comp (ineIncl h))
  have one : ∀ τ : Ine (F := E) A, a.ρ (ineIncl h τ) = 1 → τ ∈ K := fun τ e => by
    have : a.ρ.toHomUnits (ineIncl h τ) = 1 := Units.ext e
    show a.ρ.toHomUnits (ineIncl h τ) ∈ S
    rw [this]; exact S.one_mem
  have hO : IsOpen (K : Set (Ine (F := E) A)) :=
    Subgroup.isOpen_mono (H₁ := (a.ρ.comp (ineIncl h)).ker) (fun τ e => one τ e) a.smooth
  have hK : IsClosed ((K.map (Ine (F := E) A).subtype : Subgroup (G E Ω)) : Set (G E Ω)) :=
    (isClosed_Ine A).isClosedEmbedding_subtypeVal.isClosedMap _ (K.isClosed_of_isOpen hO)
  have hle : Subgroup.closure (insert γ (Wild E A : Set (G E Ω))) ≤ K.map (Ine (F := E) A).subtype := by
    rw [Subgroup.closure_le]
    rintro u (rfl | hu)
    · exact ⟨⟨u, hγ.1⟩, h1, rfl⟩
    · exact ⟨⟨u, Wild_le_Ine hu⟩, one _ (ha _ hu), rfl⟩
  obtain ⟨u, hu, e⟩ := closure_minimal (SetLike.coe_subset_coe.mpr hle) hK (hγ.2 σ.2)
  rwa [← Subtype.ext (a1 := u) (a2 := σ) e]

theorem pow_eq_one_of_roots {n : ℕ} {f : End ℂ (Fin n → ℂ)} (hf : f.IsSemisimple) {m : ℕ}
    (k : ∀ z : ℂ, f.charpoly.IsRoot z → z ^ m = 1) : f ^ m = 1 := by
  have top := hf.iSup_eigenspace_eq_top
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ ⨆ z, f.eigenspace z := top ▸ Submodule.mem_top
  induction hv using Submodule.iSup_induction' with
  | mem z x hx =>
    by_cases h0 : x = 0
    · simp [h0]
    · have he : f.HasEigenvector z x := ⟨hx, h0⟩
      rw [he.pow_apply, k z ((End.hasEigenvalue_iff_isRoot_charpoly _ _).1 (End.hasEigenvalue_of_hasEigenvector he))]
      simp
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem tor_of_ncW {y : WD h} (ht : thr w y.lpDim = 1) (k : NcW y) : UpperTheory.GalStar.Tor y := by
  obtain ⟨n, a, rfl⟩ := y.exists_rep
  have ha : a.Tame := (WD.tame_mk a).1 ((WD.tame_iff_inePol _).2 fun σ hσ => k.1 σ hσ)
  obtain ⟨γ, hγ⟩ : ∃ γ : G E Ω, TameGenAt A γ := GlobalTheory.exists_tameGenAt_of_isPlaceOver E Ω A w h
  let u := a.ρ.toHomUnits
  let g : Weil h := ineIncl h ⟨γ, hγ.1⟩
  have hq : 1 ≤ normV w := Nat.pos_of_ne_zero fun h0 => by
    have : Finite (𝓞 E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
    exact (Nat.card_pos (α := 𝓞 E ⧸ w.asIdeal)).ne' h0
  have p1 : a.ρ g ^ (normV w - 1) = 1 := pow_eq_one_of_roots (a.semisimple g) fun z hz => by
    refine k.2.2 γ hγ.1 hγ.2 z ?_
    rw [ht, WD.inePol_of_mem_Ine _ hγ.1, WD.charPol_mk]
    exact (rootMultiplicity_pos (LinearMap.charpoly_monic _).ne_zero).2 hz
  have p2 : a.ρ (frob h * g * (frob h)⁻¹) = a.ρ g := by
    rw [ha.conj_eq_pow hγ.1 deg_frob, ← Nat.sub_add_cancel hq, pow_succ, p1, one_mul]
  have c1 : Commute (u (frob h)) (u g) := by
    have e : u (frob h * g * (frob h)⁻¹) = u g := Units.ext p2
    rw [map_mul, map_mul, map_inv, mul_inv_eq_iff_eq_mul] at e
    exact e
  have cen : ∀ x : (End ℂ (Fin n → ℂ))ˣ, Commute x (u g) → ∀ σ, Commute x (u (ineIncl h σ)) := fun x hx σ =>
    Subgroup.mem_centralizer_singleton_iff.1
      (mem_of_gen ha hγ (Subgroup.centralizer {x}) (Subgroup.mem_centralizer_singleton_iff.2 hx.symm) σ) |>.symm
  have c2 := cen _ c1
  have c3 : ∀ τ σ, Commute (u (ineIncl h τ)) (u (ineIncl h σ)) := fun τ => cen _ (cen _ (Commute.refl _) τ).symm
  intro s t
  have c : Commute (u s) (u t) := by
    obtain ⟨τ, e⟩ := exists_eq_zpow_mul deg_frob s
    obtain ⟨τ', e'⟩ := exists_eq_zpow_mul deg_frob t
    rw [e, e', map_mul, map_mul, map_zpow, map_zpow]
    exact Commute.mul_left (Commute.mul_right (Commute.zpow_zpow_self _ _ _) ((c2 τ').zpow_left _))
      (Commute.mul_right ((c2 τ).symm.zpow_right _) (c3 τ τ'))
  have e : a.ρ ⁅s, t⁆ = 1 := by
    have := (map_commutatorElement u s t).trans (commutatorElement_eq_one_iff_commute.2 c)
    exact congrArg Units.val this
  show (WD.mk a).charPol _ = _
  rw [WD.charPol_mk, e, LinearMap.charpoly_one, WD.lpDim_mk]

end UpperTheory.GalS
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.UnrRecOfHasSat
section
noncomputable section

namespace UpperTheory.GalS

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
open _root_.GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.HeightCounting GlobalTheory.SmGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ}
  {HT : (E →+* Qbar l) → Multiset ℤ} {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}

omit [IsCMField E] in
theorem Aw.eq_unr {h : IsPlaceOver A w} {x y : WD h} (k : Aw x y) (hy : y.unr) : x = y := k.unr hy


end UpperTheory.GalS
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConjBis
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open _root_.GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open scoped commutatorElement

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalStar

open UpperTheory.GalS (TmW)

def IsQpBig {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) : Prop :=
  ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i ∧ (n = 1 ∨ 16 * n ^ 2 < g)

theorem IsQpBig.isQp {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ} (k : IsQpBig w n) : IsQp w := by
  obtain ⟨g, p, i, c, -⟩ := k
  exact ⟨g, p, i, c⟩

section Local
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

structure AwayB (x y : WD h) : Prop where
  dim : x.lpDim = y.lpDim

  tor : Tor y → y.mono0 → x = y

  tame0 : IsQpBig w y.lpDim → TmW y → Sqf y → y.mono0 → x.mono0 ∧ ∀ g : ↥(Weil h), deg g = 0 → x.charPol g = y.charPol g

theorem Away.big {x y : WD h} (k : Away x y) : AwayB x y := ⟨k.dim, k.tor, fun q => k.tame0 q.isQp⟩
end Local

variable (Rc : RecNotion) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]

structure AboveB (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l))
    (HT : (E →+* Qbar l) → Multiset ℤ) (P : LocPrime l) {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) : Prop where
  crys : ∀ σ, π.IsLocComp w σ → SmGL.IsSpherical σ.ρ → IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
    IsdRAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
    ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
      IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (HT τ)

  nice : ∀ σ, π.IsLocComp w σ → ∀ rc, Rc h rc → ((IsQpBig w a ∧ TmW (rc (algNorm σ)) ∧ Sqf (rc (algNorm σ))) ∨ Tor (rc (algNorm σ))) → (rc (algNorm σ)).mono0 →
    IsdRAt P Bw (r.comp (Dec (F := E) A).subtype) ∧ IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
    (∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
      IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (HT τ)) ∧
    AwayB (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)) (rc (algNorm σ))

structure PropsB (π : CuspSub E a) (ι : Qbar l ≃+* ℂ)
    (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ) : Prop where
  cont : Continuous r
  ss : IsSSRep r
  away : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (k := w.adicCompletion E) → WD h), Rc h rc → ∀ σ, π.IsLocComp w σ → AwayB (wdOf h hl ι r) (rc (algNorm σ))
  weights : ∀ τ : E →+* Qbar l, (HT τ).map (fun n : ℤ => (n : ℂ)) =
    ((CG.mk π).infChar (ι.toRingHom.comp τ)).map fun z => ((a : ℂ) - 1) / 2 - z
  weights_conj : ∀ τ : E →+* Qbar l,
    HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) = (HT τ).map (wt - ·)
  above : ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw), AboveB Rc π ι r HT P h Bw hj

def Row0b : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π χ →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ), PropsB Rc π ι r wt HT

theorem Props.big {π : CuspSub E a} {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ}
    {HT : (E →+* Qbar l) → Multiset ℤ} (k : Props Rc π ι r wt HT) : PropsB Rc π ι r wt HT :=
  ⟨k.cont, k.ss, fun w hl A h rc hrc σ hσ => (k.away w hl A h rc hrc σ hσ).big, k.weights, k.weights_conj,
    fun P AI T w A h O _ _ _ Bw hj =>
      have j := k.above P AI T w A h O Bw hj
      ⟨j.crys, fun σ hσ rc hrc g m =>
        have n := j.nice σ hσ rc hrc (g.imp (fun q => ⟨q.1.isQp, q.2⟩) id) m
        ⟨n.1, n.2.1, n.2.2.1, n.2.2.2.big⟩⟩⟩

theorem Row0.row0b (H : Row0 Rc) : Row0b Rc := fun E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hp => by
  obtain ⟨r, wt, HT, k⟩ := H E Ω l ι a ha π χ hr hp
  exact ⟨r, wt, HT, k.big Rc⟩

end UpperTheory.GalStar
end
end

