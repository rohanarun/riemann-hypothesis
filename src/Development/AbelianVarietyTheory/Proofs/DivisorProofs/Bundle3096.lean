module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3089
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2935
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0591
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0791
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2720
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2766
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalModelCartierDivisorThetaSetup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2798
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2241
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformStrictnessAndFaceCutBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHeatOperatorsAbelianLocus
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatV
open GlobalTheory.KS

theorem cst_resV {R : Type} [CommRing R] {Y : Scheme.{0}} (π : Y ⟶ Sp R) (c : R) {O : Y.Opens}
    (h : O ≤ π ⁻¹ᵁ (bo R c).1) (a : R) : cst π (bo R c).1 h (resV R c a) = constFn π O a :=
  congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.map_appLE π h (homOfLE ((Sp R).basicOpen_le (U := ⊤)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c))).op)

theorem field_cst_eq_zero {R : Type} [CommRing R] {Y : Scheme.{0}} (π : Y ⟶ Sp R) (c : R) (dd : Fld Y)
    (hd : IsField ⊤ dd) (h0 : ∀ O a, dd O (constFn π O a) = 0) (O : Y.Opens) (h : O ≤ π ⁻¹ᵁ (bo R c).1)
    (r : Γ(Sp R, (bo R c).1)) : dd O (cst π (bo R c).1 h r) = 0 := by
  let s : Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c
  have hu : IsUnit (resV R c c) := IsLocalization.Away.algebraMap_isUnit (S := Γ(Sp R, (Sp R).basicOpen s)) s
  obtain ⟨k, y, hy⟩ := IsLocalization.Away.surj (S := Γ(Sp R, (Sp R).basicOpen s)) s r
  have hy' : r * resV R c (c ^ k) = resV R c ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y) := by
    rw [map_pow]
    refine hy.trans ?_
    show _ = algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen s) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y))
    simp
  have e := congrArg (fun z => dd O (cst π (bo R c).1 h z)) hy'
  simp only [map_mul] at e
  have hu' : IsUnit (cst π (bo R c).1 h (resV R c (c ^ k))) := by
    rw [map_pow]
    exact (hu.pow k).map _
  rw [hd.2.1 O le_top, cst_resV π c h (c ^ k), cst_resV, h0, h0, ← cst_resV π c h (c ^ k)] at e
  exact hu'.mul_right_eq_zero.1 (by linear_combination e)

theorem exists_heat_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (c : R), c = ∏ i, tt i → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R) (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) → ∀ (Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (DV : Derivation ℤ Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), (∀ r, DV (GlobalTheory.HeatV.resV R c r) = GlobalTheory.HeatV.resV R c (D r)) → IsKS t (GlobalTheory.HeatV.bo R c).1 (GlobalTheory.HeatV.bo R c) (fun a => spMap (dualMap (GlobalTheory.HeatV.resV R c)) ≫ (tv (v' a)).left) ⇑DV Θ₁ → ∃ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → Fld t.G.left) (u : Fin n → Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (pf pf' : ∀ i, Γ(t.G.left, W i)) (hW : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⨆ i, W i = t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 ∧ (∀ i, W i ≤ t.PP.L.U (j i)) ∧ (∀ i, IsField (W i) (d i)) ∧ (∀ i O (h : O ≤ W i) (a : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), d i O (GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) a) = GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) (DV a)) ∧ (∀ (k : ℕ) i i' O (h : O ≤ W i ⊓ W i') (f : Γ(t.G.left, O)), GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i) (pf i) (pf' i) k O (h.trans (inf_le_left.trans (hW i))) (pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * f) = pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i') (pf i') (pf' i') k O (h.trans (inf_le_right.trans (hW i'))) f) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam _ htt hab c hc n v' D dd' hdd Θ₁ DV _ hKS
  obtain ⟨J, W, j, d, hW, hcov, hWj, hfld, hlift, hdiff⟩ :=
    ksRel_operators E H R t P m tt htt hab c hc n v' dd' hdd DV Θ₁ hKS
  have hsym := isKS_symm_abLocus E H R t P m tt htt hab c hc n v' dd' hdd DV Θ₁ hKS
  have hkill : ∀ a O (h : O ≤ t.G.hom ⁻¹ᵁ (bo R c).1) (r : Γ(Sp R, (bo R c).1)),
      dd' a O (cst t.G.hom (bo R c).1 h r) = 0 := fun a O h r =>
    field_cst_eq_zero t.G.hom c (dd' a) (hdd a).1
      (fun O' b => GlobalTheory.Heat.Adjust.inv_constFn t.G (v' a) (dd' a) (hdd a) O' b) O h r
  have h2 : IsUnit (2 : Γ(Sp R, (bo R c).1)) := by
    have : IsUnit ((2 : ℚ)) := by norm_num
    have h' := (this.map (algebraMap ℚ R)).map (resV R c)
    rwa [map_ofNat, map_ofNat] at h'
  obtain ⟨e, u, pf, pf', hglue⟩ := GlobalTheory.HeatVAlg.exists_heatV t.G.left (Sp R) t.G.hom (bo R c).1 t.PP.L t.PP.isLB h2 n
    dd' (fun a => (hdd a).1) hkill Θ₁ hsym J W j d hW hWj hfld hdiff
    (GlobalTheory.CechH1Local.exists_dlog_add_coboundary_abLocus E H R t P m tt htt hab c hc n v' dd' hdd J W j hW hcov hWj)
  refine ⟨J, W, j, fun i O' f' => d i O' f' + ∑ a, pbT t.G.hom (e a) O' * dd' a O' f', u, pf, pf', hW, hcov, hWj,
    fun i => ?_, fun i O h a => ?_, hglue⟩
  · have hF := GlobalTheory.Heat.Adjust.isField_add_comb (d i) dd' (fun a => pbT t.G.hom (e a) (W i)) (hfld i)
      fun a => (hdd a).1
    have r : ∀ O, O ≤ W i → ∀ a, rsT (pbT t.G.hom (e a) (W i)) O = pbT t.G.hom (e a) O :=
      fun O h a => rsT_pbT t.G.hom (hW i) h _
    refine ⟨fun O h f f' => ?_, fun O h f f' => ?_, fun O O' hh h f => ?_⟩
    · simpa only [r O h] using hF.1 O h f f'
    · simpa only [r O h] using hF.2.1 O h f f'
    · simpa only [r O h, r O' (hh.trans h)] using hF.2.2 O O' hh h f
  · simp only [hlift i O h a, hkill, mul_zero, Finset.sum_const_zero, add_zero]

end GlobalTheory.HeatV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeToPHeckeTranslateHarrisTaylor
section
noncomputable section

namespace GlobalTheory.UPel.HT.Hecke

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem exists_isHecke : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∃ (o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsHecke g c k N o o' ψ := by
  intro p _ D R _ b g c k N hc hk hN hNp hEF hg hck S s o
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hk; exact (Fact.out : p.Prime).one_lt.ne' hk)
  have hN0 : 0 < N := by omega
  obtain ⟨hfin, hfree⟩ := GlobalTheory.UPel.HT.Hecke.heckeSub_finite_free p D R b g k N hk0 hN0 hk hNp S s o
  obtain ⟨A', _, _, ψ, hA', hψ, hgal⟩ := GlobalTheory.TranslQuotient.exists_quotient S o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left)
    (heckeSub o g N) o.ab (pull_isLB o.isLB _) o.ample hfin hfree
  have hepi : Epi ψ := by
    have := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hgal
    exact (Over.forget S).epi_of_epi_map this
  have kill : ∀ h ∈ heckeSub o g N, h ≫ ψ = 1 := fun h hh =>
    comp_eq_one_of_transl ψ h (hgal.inv ⟨h, hh⟩)
  have stab : ∀ c' : D.O, ∀ h ∈ heckeSub o g N, h ≫ o.act.act c' ∈ heckeSub o g N := by
    rintro c' _ ⟨x, rfl⟩
    refine ⟨c' • x, ?_⟩
    rw [← o.eta_lin, map_smul, smul_comm]
  choose actf hactf using fun c' : D.O => GlobalTheory.UPel.HT.Hecke.exists_desc_endo S o.A A' (heckeSub o g N) ψ hψ hgal (o.act.act c') (o.act.hom c') (stab c')
  let act' : OActN D.O A' :=
    { act := actf
      hom := fun c' => (hactf c').1
      one := by
        rw [← cancel_epi ψ, (hactf 1).2, o.act.one, Category.id_comp, Category.comp_id]
      mul := fun b' c' => by
        rw [← cancel_epi ψ, (hactf _).2, o.act.mul, Category.assoc, ← (hactf b').2, ← Category.assoc,
          ← (hactf c').2, Category.assoc]
      add := fun b' c' => by
        rw [← cancel_epi ψ, (hactf _).2, o.act.add, mul_comp, comp_mul, (hactf _).2, (hactf _).2] }
  have hcomp : ∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c' := fun c' => ((hactf c').2).symm
  obtain ⟨P', hP', r1, r2, hsym, hamp, hker, hros, hpull⟩ :=
    GlobalTheory.T.exists_hecke_translate_polarisation_bundle p D R b g c k N hc hk hN hNp hEF hg hck S s o A' act' ψ hA' hψ hgal hcomp
  obtain ⟨hlie, hlieR⟩ := GlobalTheory.UPel.HT.EtaleLie.lie_of_etale p D R b (N * k) S s o A' act' ψ _ _ hA' hψ hgal hcomp
  have hgeom := _root_.GlobalTheory.UPel.HT.Hecke.TateTransl.exists_tateIsoO_transl p D R b g c k N hc hk hN hNp hEF hg hck S s o A' act' ψ hA' hψ hgal hcomp P' hP' r1 r2 hpull
  let o' : Obj b N s :=
    { A := A'
      ab := hA'
      act := act'
      P := P'
      isLB := hP'
      rig₁ := r1
      rig₂ := r2
      symm := hsym
      ample := hamp
      kerP := hker
      rosati := hros
      lie := hlie
      lieRank := hlieR
      eta := fun x => o.eta (g x) ≫ ψ
      eta_add := fun x y => by rw [map_add (f := _), o.eta_add, mul_comp]
      eta_lin := fun c' x => by
        show o.eta (g (c' • x)) ≫ ψ = (o.eta (g x) ≫ ψ) ≫ act'.act c'
        rw [map_smul, o.eta_lin, Category.assoc, hcomp, Category.assoc]
      eta_ker := fun x => by rw [map_nsmul]; exact kill _ (mem_heckeSub o g N x)
      geom := hgeom }
  exact ⟨o', ψ, hψ, hcomp, fun x => rfl, hgal, ⟨hpull⟩, hck⟩

end GlobalTheory.UPel.HT.Hecke
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepAdjointActionLevelSiegelPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rep_adjointAction_level_siegelPullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∃ (E : Scheme.{0}) (πE : E ⟶ S) (AE : Over E) (_ : GrpObj AE) (_ : IsCommMonObj AE) (φE : AE.left ⟶ c.A.left) (φ₂E : (G2 AE).left ⟶ (G2 c.A).left) (actE : OActN D.O AE) (ηE : D.La → (𝟙_ (Over E) ⟶ AE)), IsLocallyNoetherian E ∧ IsFinite πE ∧ IsGrpPullback AE c.A πE φE ∧ IsSquare φE φ₂E ∧ RosatiFor D actE (c.P.pull φ₂E) ∧ EtaOK D N actE ηE ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (AT : Over T) [GrpObj AT] (φ : AT.left ⟶ c.A.left) (φ₂ : (G2 AT).left ⟶ (G2 c.A).left) (act : OActN D.O AT) (eta : D.La → (𝟙_ (Over T) ⟶ AT)), IsGrpPullback AT c.A g φ → IsSquare φ φ₂ → RosatiFor D act (c.P.pull φ₂) → EtaOK D N act eta → ∃! z : T ⟶ E, z ≫ πE = g ∧ ∃ ψ : AT.left ⟶ AE.left, IsGrpPullback AT AE z ψ ∧ ψ ≫ φE = φ ∧ (∀ a : D.O, (act.act a).left ≫ ψ = ψ ≫ (actE.act a).left) ∧ ∀ y, (eta y).left ≫ ψ = z ≫ (ηE y).left := by
  first | (exact @GlobalTheory.UPel.HT.exists_finite_rep_rosati_level) | (exact GlobalTheory.UPel.HT.exists_finite_rep_rosati_level) | (intros; apply GlobalTheory.UPel.HT.exists_finite_rep_rosati_level  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricKodairaSpencerAbelianLocusStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_kodairaSpencer_abelianLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (DV : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)), ∃ Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1), Θ₁ᵀ = Θ₁ ∧ IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (fun a => spMap (dualMap (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) ≫ (tv (v' a)).left) ⇑DV Θ₁ := by
  first | exact @GlobalTheory.KSAbLocusSymm.exists_symm_isKS_abLocus | exact GlobalTheory.KSAbLocusSymm.exists_symm_isKS_abLocus | (intros; apply GlobalTheory.KSAbLocusSymm.exists_symm_isKS_abLocus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupIdealOverClopenComponent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.Poinc.exists_setup_ideal_over_component : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∃ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι ∧ Set.range X₁.π = W ∧ (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a} := by
  intro g n hg hn hodd F Z z i hθ φ hφ W hWc hWi
  obtain ⟨hproj, hnorm, hopen, hcomp, hdense, W8, hE8, hTI⟩ := id hθ
  obtain ⟨η, hη, hcl⟩ := GlobalTheory.exists_mem_genericPoints_closure_eq_of_isClopen F.X Z i hopen hdense W hWc hWi
  obtain ⟨X₁, -, hX₁⟩ := GlobalTheory.Poinc.GSetup.exists_setup g n hg hn hodd F Z z i hproj
    (fun x => ⟨hnorm.isDomain_stalk x, hnorm.isIntegrallyClosed_stalk x⟩) hopen hcomp hdense W8 hE8 hTI η hη 0
  have hr := GlobalTheory.Poinc.Setup.range_π_eq g n F W8 Z i X₁ η W hX₁ hcl
  obtain ⟨ι, Y, πY, D, hι, hhom, hprop, hnY, hsupp, hord⟩ := _root_.GlobalTheory.Poinc.exists_model_divisor_of_orders g n hg hn hodd F Z z i hθ φ hφ W8 hE8 hTI X₁
  obtain ⟨ι', J₁, hι', hsupp', hord'⟩ :=
    _root_.GlobalTheory.Poinc.DescentPow.exists_idealSheaf_comap_orders g n hg hn hodd F Z z i hθ φ hφ W8 hE8 hTI X₁ ι Y πY D hι X₁.projM hhom hprop hnY hsupp hord
  have hhomog : ∀ (T : Trait F) (k : ℕ), 1 ≤ k → φ.evalZ ((k : ℤ) • T.β) = k * φ.evalZ T.β := by
    intro T k _
    have hrk : Module.finrank ℤ T.D.toPre.X ≤ g := by
      have := GlobalTheory.Poinc.Trait.dim_add_rank (by omega : 2 ≤ n) F T
      omega
    have hβ : T.β ∈ balForms (id : ℤ → ℤ) T.D.toPre.X := ⟨T.symm, fun a y z => by simp⟩
    rw [natCast_zsmul, StrictData.evalZ_eq, StrictData.evalZ_eq, StrictData.toReal_nsmul]
    exact (hφ _ hrk).homog _ (StrictData.toReal_mem_psdCone hβ fun y => T.mono.nonneg 0 y) _ (Nat.cast_nonneg k)
  obtain ⟨hs, ho⟩ := GlobalTheory.Poinc.ideal_orders_of_proper_model g n F W8 Z i φ X₁ Y πY hhom hprop ι' J₁ hsupp' hord' hhomog
  exact ⟨W8, X₁, ι', J₁, hι', hr, hs, ho⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveQcPow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UPel.HT.SiegUniqBase

section FlatPow
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj CategoryTheory.MonObj

theorem flat_surjective_qc_pow : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ k : ℕ, 0 < k → Flat ((𝟙 A) ^ k).left ∧ Surjective ((𝟙 A) ^ k).left ∧ QuasiCompact ((𝟙 A) ^ k).left := by
  intro S A _ hA k hk
  have hc := hA.comm
  obtain ⟨h1, h2⟩ := GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA S A hA k hk
  have e : (𝟙 A) ^ k = ReciprocityTheory.ChartRestriction.G.Out.mulA A k := rfl
  rw [e]
  refine ⟨h2, GlobalTheory.AbLaw.MulN.surjective_of_geomFibres _ fun K _ _ t => ?_, inferInstance⟩
  have hf : IsFinite ((Over.pullback t).map (ReciprocityTheory.ChartRestriction.G.Out.mulA A k)).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) h1
  rw [GlobalTheory.MulFiniteFlat.pullback_map_mulA] at hf ⊢
  have hB := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A hA
  have hBc := hB.comm
  exact (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
    hB _ (GlobalTheory.AbLaw.MulN.isMonHom_mulA _ k) hf).2

end FlatPow

end GlobalTheory.UPel.HT.SiegUniqBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorCrystalActionAdjointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_crystal_action_adjoint : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (c : D.O) x y, φ (GlobalTheory.HTCount.crysAct o₀ c x) y = φ x (GlobalTheory.HTCount.crysAct o₀ (D.star c).unop y) := by
  first | (exact @GlobalTheory.HTCount.crysAct_adjoint) | (exact GlobalTheory.HTCount.crysAct_adjoint) | (intros; apply GlobalTheory.HTCount.crysAct_adjoint  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsLiftOrderActionHodgeSummandStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_exists_lift_orderAction_hodge_summand : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ (E : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A)), (∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl E M) → (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr d y) → (∀ (c : D.O), ∀ d ∈ E, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (d)) ∈ E) → ∃ (A : Over (Sp C)) (_ : GrpObj A) (i : o₀.A.left ⟶ A.left) (h : IsGrpPullback o₀.A A (spMap π) i) (act : GlobalTheory.UPel.HT.OActN D.O A), IsAbelianScheme A ∧ liftFil (divided₂ hsq) h = E ∧ ∀ c, (o₀.act.act c).left ≫ i = i ≫ (act.act c).left := by
  first | exact @GlobalTheory.HTDeform.exists_lift_oAct | exact GlobalTheory.HTDeform.exists_lift_oAct | (intros; apply GlobalTheory.HTDeform.exists_lift_oAct <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorHodgeFiltrationNaturality
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HTUniv.Nat

open GlobalTheory.CechPic GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

theorem pull_cls_diag {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o : Obj b N s} {o' : Obj b N s'}
    {f : S' ⟶ S} (mp : ObjMap o' o f) :
    pull mp.φ (cls (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (pull_isLB o.isLB _)) =
      cls (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) (pull_isLB o'.isLB _) := by
  have hs := mp.sq
  have e : (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ mp.φ₂ = mp.φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left := by
    have a₁ := congrArg (fun q => q.left) (lift_fst (𝟙 o.A) (𝟙 o.A))
    have a₂ := congrArg (fun q => q.left) (lift_snd (𝟙 o.A) (𝟙 o.A))
    have b₁ := congrArg (fun q => q.left) (lift_fst (𝟙 o'.A) (𝟙 o'.A))
    have b₂ := congrArg (fun q => q.left) (lift_snd (𝟙 o'.A) (𝟙 o'.A))
    simp only [Over.comp_left, Over.id_left] at a₁ a₂ b₁ b₂
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst o.A o.A).left = (_ ≫ _) ≫ (fst o.A o.A).left
      rw [Category.assoc, hs.1, ← Category.assoc, b₁, Category.assoc, a₁]; simp
    · show (_ ≫ _) ≫ (snd o.A o.A).left = (_ ≫ _) ≫ (snd o.A o.A).left
      rw [Category.assoc, hs.2, ← Category.assoc, b₂, Category.assoc, a₂]; simp
  have h1 : pull mp.φ₂ (cls o.P o.isLB) = cls o'.P o'.isLB :=
    ((cls_eq_iff o'.isLB (pull_isLB o.isLB mp.φ₂)).2 mp.pol).symm
  rw [cls_pull o.isLB, cls_pull o'.isLB, ← pull_comp, ← e, pull_comp, h1]

theorem phi_eq (hN : 3 ≤ N) (hNp : N.Coprime p) {k : Type} [Field k] [IsAlgClosed k] {t : Sp k ⟶ Sp R}
    (o₀ : Obj b N t) {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) {z : Sp k ⟶ S}
    {φ φ' : o₀.A.left ⟶ o.A.left} (h : IsGrpPullback o₀.A o.A z φ) (h' : IsGrpPullback o₀.A o.A z φ')
    (hc : pull φ (cls (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (pull_isLB o.isLB _)) =
      pull φ' (cls (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (pull_isLB o.isLB _)))
    (he : ∀ y, (o₀.eta y).left ≫ φ = z ≫ (o.eta y).left) (he' : ∀ y, (o₀.eta y).left ≫ φ' = z ≫ (o.eta y).left) :
    φ = φ' := by
  have hN0 : 0 < N := by omega
  have hNK : (N : k) ≠ 0 := by
    have hu := (b.unit N hNp).map (Spec.preimage t).hom
    rw [map_natCast] at hu
    exact hu.ne_zero
  refine GlobalTheory.SiegRigid.eq_of_field (pull_isLB o.isLB _) o.ample o₀.ab h h' hc hN hNK fun Ω _ _ x y hy => ?_
  obtain ⟨I, hI⟩ := o₀.geom Ω x (Spec.preimage (x ≫ t)).hom (Spec.map_preimage _).symm
  obtain ⟨a, ha⟩ := (I.onto N hN0 hNp y).1 hy
  rw [← ha, ← hI a]
  simp only [Over.comp_left, Category.assoc, he, he']

theorem corr_of_isBC {R₀ R₁ R₂ : Type} [CommRing R₀] [CommRing R₁] [CommRing R₂] [Algebra R₀ R₁]
    {I₀ : Ideal R₀} {I₁ : Ideal R₁} {I₂ : Ideal R₂} {κ₀ : DividedPowers I₀} {κ₁ : DividedPowers I₁}
    {κ₂ : DividedPowers I₂} {S₀ S₁ S₂ : Scheme.{0}} {t₀ : S₀ ⟶ Sp R₀} {t₁ : S₁ ⟶ Sp R₁} {t₂ : S₂ ⟶ Sp R₂}
    {A₀ : Over S₀} {A₁ : Over S₁} {A₂ : Over S₂} [GrpObj A₀] [GrpObj A₁] [GrpObj A₂] {b₁ : S₁ ⟶ S₀}
    {b₂ : S₂ ⟶ S₁} {φ₁ : A₁.left ⟶ A₀.left} {φ₂ : A₂.left ⟶ A₁.left} {σ : R₁ →+* R₂}
    {m : GrpMor κ₀ t₀ A₀ κ₁ t₁ A₁ (algebraMap R₀ R₁) b₁ φ₁} (hm : m.IsBC)
    (M : GrpMor κ₁ t₁ A₁ κ₂ t₂ A₂ σ b₂ φ₂) {h : Crys κ₁ t₁ A₁} {h' : Crys κ₂ t₂ A₂}
    (e : ∀ q, h' (M.pull (m.pull q)) = σ (h (m.pull q))) : M.Corr h h' := by
  intro q
  obtain ⟨w, rfl⟩ := hm.2 q
  induction w with
  | add u v hu hv => simp only [map_add (f := _), hu, hv]
  | tmul r q =>
    rw [liftSemi_tmul, LinearMap.map_smulₛₗ, map_smul, map_smul, e, smul_eq_mul, smul_eq_mul, map_mul]


set_option maxHeartbeats 1000000 in
theorem main : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∀ (d : ℕ) (s : Sp (TrivSqZeroExt k (Fin d → k)) ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)) (c : (Fin d → k) →ₗ[k] k) (s' : Sp (DualNumber k) ⟶ Sp R) (o' : GlobalTheory.UPel.HT.Obj b N s') (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (n : GlobalTheory.UPel.HT.ObjMap o' o (spMap (TrivSqZeroExt.map c).toRingHom)) (x : HdR o₀.A) (y : primDR o₀.A →ₗ[k] (Fin d → k)), GlobalTheory.FODef.IsFilLiftV m.cart x y → IsFilLift m'.cart x (c ∘ₗ y) := by
  intro p _ D R _ b N hN hNp k _ _ t o₀ d s o m c s' o' m' n x y hxy
  obtain ⟨dd, hdd, edd⟩ := hxy
  let σ : TrivSqZeroExt k (Fin d → k) →+* DualNumber k := (TrivSqZeroExt.map c).toRingHom
  have hz : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap σ =
      spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom := by
    rw [← Cris.spMap_comp]
    congr 1
    ext a <;> simp [σ]

  have hrig : m'.φ ≫ n.φ = m.φ := by
    refine (phi_eq hN hNp o₀ o ((m'.cart.comp n.cart).congr hz rfl) m.cart ?_ ?_ m.eta).symm.symm
    · rw [pull_comp, pull_cls_diag n, pull_cls_diag m', pull_cls_diag m]
    · intro y
      rw [← Category.assoc, m'.eta y, Category.assoc, n.eta y, ← Category.assoc, hz]

  have hdp : (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))).IsDPMorphism (epsDP k) σ := by
    unfold epsDP
    refine isDPMorphism_sqDP _ _ σ fun a ha => ?_
    have ha' : a.fst = 0 := ha
    change (σ a).fst = 0
    simp [σ, ha']
  have M : GrpMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)
      o₀.A (epsDP k) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A σ (𝟙 _) (Over.Hom.left (𝟙 o₀.A)) :=
    GrpMor.of_hom hdp hz.symm (𝟙 o₀.A)
  have hBC : (constMor o₀.A).IsBC := GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k k o₀.A o₀.ab _ (constMor o₀.A)
  have hBCV : (GlobalTheory.FODef.constMorV k (Fin d → k) o₀.A).IsBC :=
    GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k (Fin d → k) o₀.A o₀.ab _ _
  let d' : Crys (epsDP k) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A :=
    hBC.bcMap x + (TrivSqZeroExt.inr (1 : k) : DualNumber k) • hBC.bcMap (c ∘ₗ y)
  have ed' : ∀ q, d' ((constMor o₀.A).pull q) = TrivSqZeroExt.inl (x q) + TrivSqZeroExt.inr (c (y q)) := by
    intro q
    have e1 := (hBC.corr_iff (h := x)).2 rfl q
    have e2 := (hBC.corr_iff (h := c ∘ₗ y)).2 rfl q
    simp only [d', LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, e1, e2]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hMc : M.Corr dd d' := corr_of_isBC hBCV M fun q => by
    rw [GrpMor.pull_pull (GlobalTheory.FODef.constMorV k (Fin d → k) o₀.A) M (constMor o₀.A) (fun _ => by
      ext <;> simp [σ, TrivSqZeroExt.algebraMap_eq_inl]) (by simp) q, ed', edd q]
    ext <;> simp [σ]
  have Nm : GrpMor (dp0 _) (𝟙 _) o.A (dp0 _) (𝟙 _) o'.A σ (spMap σ) n.φ :=
    GrpMor.of_isGrpPullback (isDPMorphism_of_eq_bot _ rfl _ _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) n.cart
  have hNc := crysToDR_corr (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) m.cart m'.cart M Nm
    (by rw [hrig]; simp) hMc
  refine ⟨d', ?_, fun q => ?_⟩
  · letI : Algebra (TrivSqZeroExt k (Fin d → k)) (DualNumber k) := σ.toAlgebra
    obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim (TrivSqZeroExt k (Fin d → k)) o.A o.ab
    have hF := (GlobalTheory.abelianDeRham.2.2.1 _ o.A g o.ab hg (DualNumber k) o'.A n.φ n.cart).2
    exact mem_Fil_of_corr (hφ := n.cart) hF hNc hdd
  · rw [ed']
    rfl

end GlobalTheory.HTUniv.Nat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionIdentityOfHodgeSummandStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_lie_condition_identity_of_hodge_summand : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : o₀.A.left ⟶ A.left) (h : IsGrpPullback o₀.A A (spMap π) i), IsAbelianScheme A → ∀ (act : GlobalTheory.UPel.HT.OActN D.O A), (∀ c, (o₀.act.act c).left ≫ i = i ≫ (act.act c).left) → (∀ d : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (d)) - tR b.ρ • d ∈ liftFil (divided₂ hsq) h → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ liftFil (divided₂ hsq) h) ∧ d - ∑ i, w i ∈ liftFil (divided₂ hsq) h) → GlobalTheory.UPel.HT.LieAt b act tR (spMap (RingHom.id C)) := by
  first | (exact @GlobalTheory.HTLieCrys.lieAt_id_of_liftFil) | (exact GlobalTheory.HTLieCrys.lieAt_id_of_liftFil) | (intros; apply GlobalTheory.HTLieCrys.lieAt_id_of_liftFil <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionModHodgeFiltrationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_lie_condition_mod_hodgeFiltration : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C₀ : Type) [CommRing C₀] [IsLocalRing C₀] (β : R →+* C₀) (s : Sp C₀ ⟶ Sp R), s = spMap β → ∀ (o₀ : GlobalTheory.UPel.HT.Obj b N s) (y : HdR o₀.A), GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) o₀.act (algebraMap (𝓞 D.F) D.O D.ω) y - β b.ρ • y ∈ Fil o₀.A → ∃ w : Fin D.a → HdR o₀.A, (∀ i (c : 𝓞 D.F), GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) o₀.act (algebraMap (𝓞 D.F) D.O c) (w i) - β (b.t i c) • w i ∈ Fil o₀.A) ∧ y - ∑ i, w i ∈ Fil o₀.A := by
  first | (exact @GlobalTheory.HTSummand.lie_mod_fil) | (exact GlobalTheory.HTSummand.lie_mod_fil) | (intros; apply GlobalTheory.HTSummand.lie_mod_fil  <;> assumption)
end

