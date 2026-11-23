module

public import Mathlib
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0631
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0647
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatLoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0638
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0639
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0637
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0636
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHolomorphicIffChartHolomorphic
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem holo_etale_iff_holo_chart : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ (Ω : Set Y) (u : Y → ℂ), IsOpen Ω → ((∀ e : OpenPartialHomeomorph U (V n), IsChart n (fun y : U => z y) e → DifferentiableOn ℂ ((fun y : U => u y) ∘ e.symm) (e.target ∩ e.symm ⁻¹' (Subtype.val ⁻¹' Ω))) ↔ ∀ i, DifferentiableOn ℂ (u ∘ (A.chart i).symm) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω))) := by
  intro n Y _ _ _ _ _ ι La _ A U z hE Ω u hΩ
  have hloc := _root_.GlobalTheory.OTY.etale_isLocalHomeomorph n Y ι La A U z hE
  constructor
  · intro h i v hv
    obtain ⟨hvt, hvU, hvΩ⟩ := hv
    obtain ⟨e, hes, hez⟩ := hloc ⟨(A.chart i).symm v, hvU⟩
    have he : IsChart n (fun y : U => z y) e := fun w _ => by rw [hez]
    have hev : ∀ w : U, e w = z w := fun w => by rw [← hez]
    obtain ⟨W, hW, hWe⟩ := isOpen_induced_iff.1 e.open_source
    have hO : IsOpen (e.target ∩ e.symm ⁻¹' (Subtype.val ⁻¹' Ω)) :=
      e.isOpen_inter_preimage_symm (hΩ.preimage continuous_subtype_val)
    have hmem : z ((A.chart i).symm v) ∈ e.target ∩ e.symm ⁻¹' (Subtype.val ⁻¹' Ω) := by
      have h1 := hev ⟨(A.chart i).symm v, hvU⟩
      simp only at h1
      rw [← h1]
      refine ⟨e.map_source hes, ?_⟩
      simp only [Set.mem_preimage]
      rw [e.left_inv hes]
      exact hvΩ
    have h1 : DifferentiableAt ℂ ((fun y : U => u y) ∘ e.symm) (z ((A.chart i).symm v)) :=
      (h e he _ hmem).differentiableAt (hO.mem_nhds hmem)
    have h2 : DifferentiableAt ℂ (z ∘ (A.chart i).symm) v :=
      (hE.holo i v ⟨hvt, hvU⟩).differentiableAt
        (((A.chart i).isOpen_inter_preimage_symm hE.isOpen).mem_nhds ⟨hvt, hvU⟩)
    have h3 := DifferentiableAt.comp v (g := (fun y : U => u y) ∘ e.symm)
      (f := z ∘ (A.chart i).symm) h1 h2
    refine (h3.congr_of_eventuallyEq ?_).differentiableWithinAt
    have hvW : (A.chart i).symm v ∈ W := by
      rw [← hWe] at hes
      exact hes
    filter_upwards [((A.chart i).isOpen_inter_preimage_symm (hE.isOpen.inter hW)).mem_nhds
      ⟨hvt, hvU, hvW⟩] with v' hv'
    have hs : (⟨(A.chart i).symm v', hv'.2.1⟩ : U) ∈ e.source := by
      rw [← hWe]
      exact hv'.2.2
    have h4 := hev ⟨(A.chart i).symm v', hv'.2.1⟩
    simp only at h4
    simp only [Function.comp]
    rw [← h4, e.left_inv hs]
  · intro h e he v hv
    obtain ⟨hvt, hvΩ⟩ := hv
    have hs := A.mem_pick (e.symm v : U)
    set i := A.pick (e.symm v : U)
    obtain ⟨hc, hev, -⟩ := _root_.GlobalTheory.OTY.etale_local_inverse n Y ι La A U z hE e he v hvt i hs
    have hmem : A.chart i (e.symm v : U) ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω) := by
      refine ⟨(A.chart i).map_source hs, ?_⟩
      simp only [Set.mem_preimage]
      rw [(A.chart i).left_inv hs]
      exact ⟨(e.symm v).2, hvΩ⟩
    have h1 : DifferentiableAt ℂ (u ∘ (A.chart i).symm) (A.chart i (e.symm v : U)) :=
      (h i _ hmem).differentiableAt
        (((A.chart i).isOpen_inter_preimage_symm (hE.isOpen.inter hΩ)).mem_nhds hmem)
    have h3 := DifferentiableAt.comp v (g := u ∘ (A.chart i).symm)
      (f := fun v' => A.chart i (e.symm v' : U)) h1 (hc.differentiableAt (by simp))
    refine (h3.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hev] with v' hv'
    simp only [Function.comp]
    rw [(A.chart i).left_inv hv']

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfFilteredColimit
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.EtC.PolyColim

variable {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0})

def polyDiag : J ⥤ CommRingCat.{0} where
  obj j := CommRingCat.of (Polynomial (D.obj j))
  map f := CommRingCat.ofHom (Polynomial.mapRingHom (D.map f).hom)
  map_id j := by
    refine CommRingCat.hom_ext (RingHom.ext fun p => ?_)
    simp
  map_comp f g := by
    refine CommRingCat.hom_ext (RingHom.ext fun p => ?_)
    simp [Polynomial.map_map]

def polyCocone (c : Cocone D) : Cocone (polyDiag D) where
  pt := CommRingCat.of (Polynomial c.pt)
  ι :=
    { app := fun j => CommRingCat.ofHom (Polynomial.mapRingHom (c.ι.app j).hom)
      naturality := fun i j f => by
        refine CommRingCat.hom_ext (RingHom.ext fun p => ?_)
        exact (Polynomial.map_map (D.map f).hom (c.ι.app j).hom (show Polynomial (D.obj i) from p)).trans
          (congrArg (fun g => Polynomial.map g (show Polynomial (D.obj i) from p))
            (by rw [← CommRingCat.hom_comp, c.w f])) }

variable {D} [IsFiltered J]

open CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) in
variable {D} [IsFiltered J] in
private lemma exists_map_eq_zero_of_isColimit_lemma {c : Cocone D} (hc : IsColimit c) {j : J}
    (x : D.obj j) (h : (c.ι.app j).hom x = 0) : ∃ (k : J) (f : j ⟶ k), (D.map f).hom x = 0 := by
  obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq D hc x 0 (by simpa using h)
  exact ⟨k, f, by simpa using hfg⟩

open CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) in
variable {D} [IsFiltered J] in
theorem _root_.GlobalTheory.EtC.PolyColim.poly_exists_map_eq_zero {c : Cocone D} (hc : IsColimit c) {j : J}
    (p : Polynomial (D.obj j))
    (h : p.map (c.ι.app j).hom = 0) : ∃ (k : J) (f : j ⟶ k), p.map (D.map f).hom = 0 := by
  have key : ∀ s : Finset ℕ, ∃ (k : J) (f : j ⟶ k), ∀ n ∈ s, (D.map f).hom (p.coeff n) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨j, 𝟙 j, by simp⟩
    | insert a s _ ih =>
      obtain ⟨k, f, hf⟩ := ih
      have ha : (c.ι.app k).hom ((D.map f).hom (p.coeff a)) = 0 := by
        rw [← CommRingCat.comp_apply, c.w f, ← Polynomial.coeff_map, h, Polynomial.coeff_zero]
      obtain ⟨k', f', hf'⟩ := exists_map_eq_zero_of_isColimit_lemma hc _ ha
      refine ⟨k', f ≫ f', fun n hn => ?_⟩
      rw [D.map_comp, CommRingCat.comp_apply]
      rcases Finset.mem_insert.mp hn with rfl | hn
      · exact hf'
      · rw [hf n hn, map_zero]
  obtain ⟨k, f, hf⟩ := key p.support
  refine ⟨k, f, Polynomial.ext fun n => ?_⟩
  rw [Polynomial.coeff_map, Polynomial.coeff_zero]
  by_cases hn : n ∈ p.support
  · exact hf n hn
  · rw [Polynomial.notMem_support_iff.mp hn, map_zero]

open CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) in
variable {D} [IsFiltered J] in
private lemma exists_rep_of_isColimit_lemma_2 {c : Cocone D} (hc : IsColimit c) (x : c.pt) :
    ∃ (j : J) (y : D.obj j), (c.ι.app j).hom y = x := by
  obtain ⟨j, y, hy⟩ := Concrete.isColimit_exists_rep D hc x
  exact ⟨j, y, hy⟩

open CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) in
variable {D} [IsFiltered J] in
theorem _root_.GlobalTheory.EtC.PolyColim.poly_exists_rep {c : Cocone D} (hc : IsColimit c)
    (p : Polynomial c.pt) :
    ∃ (j : J) (y : Polynomial (D.obj j)), y.map (c.ι.app j).hom = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨i, y, hy⟩ := hp
    obtain ⟨j, z, hz⟩ := hq
    refine ⟨IsFiltered.max i j, y.map (D.map (IsFiltered.leftToMax i j)).hom +
      z.map (D.map (IsFiltered.rightToMax i j)).hom, ?_⟩
    rw [Polynomial.map_add (f := _), Polynomial.map_map, Polynomial.map_map, ← CommRingCat.hom_comp,
      ← CommRingCat.hom_comp, c.w, c.w, hy, hz]
  | monomial n a =>
    obtain ⟨j, y, hy⟩ := exists_rep_of_isColimit_lemma_2 hc a
    exact ⟨j, Polynomial.monomial n y, by rw [Polynomial.map_monomial, hy]⟩

def polyCoconeIsColimit {c : Cocone D} (hc : IsColimit c) : IsColimit (polyCocone D c) := by
  haveI : ReflectsColimitsOfShape J (forget CommRingCat.{0}) := reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (forget CommRingCat.{0})
    (Types.FilteredColimit.isColimitOf _ ((forget CommRingCat.{0}).mapCocone (polyCocone D c)) ?_ ?_)
  · intro x
    obtain ⟨j, y, hy⟩ := poly_exists_rep hc (show Polynomial c.pt from x)
    exact ⟨j, y, hy.symm⟩
  · intro i j xi xj h
    change Polynomial.map (c.ι.app i).hom xi = Polynomial.map (c.ι.app j).hom xj at h
    obtain ⟨k, f, hf⟩ := poly_exists_map_eq_zero hc (j := IsFiltered.max i j)
      ((show Polynomial (D.obj i) from xi).map (D.map (IsFiltered.leftToMax i j)).hom -
        (show Polynomial (D.obj j) from xj).map (D.map (IsFiltered.rightToMax i j)).hom) (by
        rw [Polynomial.map_sub, Polynomial.map_map, Polynomial.map_map, ← CommRingCat.hom_comp,
          ← CommRingCat.hom_comp, c.w, c.w, h, sub_self])
    refine ⟨k, IsFiltered.leftToMax i j ≫ f, IsFiltered.rightToMax i j ≫ f, ?_⟩
    change Polynomial.map (D.map (IsFiltered.leftToMax i j ≫ f)).hom xi =
      Polynomial.map (D.map (IsFiltered.rightToMax i j ≫ f)).hom xj
    rw [Polynomial.map_sub, Polynomial.map_map, Polynomial.map_map, ← CommRingCat.hom_comp,
      ← CommRingCat.hom_comp, ← Functor.map_comp, ← Functor.map_comp, sub_eq_zero] at hf
    exact hf

end GlobalTheory.EtC.PolyColim

namespace GlobalTheory.EtC

theorem pull_spMap_comp (R : Type) [CommRing R] {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (F : Shv R) (n : ℤ) (x : H R (sp A) F n) :
    pull R (spMap (g.comp f)) F n x = pull R (spMap g) F n (pull R (spMap f) F n x) := by
  show pull R (sch.map _) F n x = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp, pull_comp]

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show sch.map _ = sch.map _ ≫ sch.map _
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem hInv_of_filtered_colimit : ∀ (q : ℕ) [NeZero q] (J : Type) [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → (∀ j, IsUnit (q : D.obj j)) →
    (∀ j, HInv q (D.obj j)) → HInv q c.pt := by
  intro q _ J _ _ D c hc hq hH i n
  have hB : B1 := pairingProperties
  let D' := PolyColim.polyDiag D
  let c' := PolyColim.polyCocone D c
  have hc' : IsColimit c' := PolyColim.polyCoconeIsColimit hc
  obtain ⟨j0⟩ : Nonempty J := IsFiltered.nonempty
  have hqc : IsUnit (q : c.pt) := by
    have := (hq j0).map (c.ι.app j0).hom
    rwa [map_natCast] at this
  have hqP : ∀ j, IsUnit (q : D'.obj j) := fun j => by
    have := (hq j).map (Polynomial.C : D.obj j →+* Polynomial (D.obj j))
    rwa [map_natCast] at this
  have hqc' : IsUnit (q : c'.pt) := by
    have := hqc.map (Polynomial.C : c.pt →+* Polynomial c.pt)
    rwa [map_natCast] at this
  have sq : ∀ j, (c'.ι.app j).hom.comp (Polynomial.C : D.obj j →+* Polynomial (D.obj j)) =
      (Polynomial.C : c.pt →+* Polynomial c.pt).comp (c.ι.app j).hom := fun j =>
    RingHom.ext fun a => by
      change Polynomial.map (c.ι.app j).hom (Polynomial.C a) = Polynomial.C ((c.ι.app j).hom a)
      exact Polynomial.map_C _
  have sqD : ∀ {j k : J} (f : j ⟶ k), (D'.map f).hom.comp (Polynomial.C : D.obj j →+* Polynomial (D.obj j)) =
      (Polynomial.C : D.obj k →+* Polynomial (D.obj k)).comp (D.map f).hom := @fun j k f =>
    RingHom.ext fun a => by
      change Polynomial.map (D.map f).hom (Polynomial.C a) = Polynomial.C ((D.map f).hom a)
      exact Polynomial.map_C _
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨j, y, rfl⟩ := (hB q D c hc n i).1 x hqc
    have e1 : pull _ (spMap (c'.ι.app j).hom) _ _ (pull _ (spMap (Polynomial.C : D.obj j →+* Polynomial (D.obj j))) _ _ y) = 0 :=
      (pull_spMap_comp (ZMod q) Polynomial.C (c'.ι.app j).hom (tw q i) n y).symm.trans
        ((congrArg (fun g => pull (ZMod q) (spMap g) (tw q i) n y) (sq j)).trans
          ((pull_spMap_comp (ZMod q) (c.ι.app j).hom Polynomial.C (tw q i) n y).trans hx))
    obtain ⟨k, f, hf⟩ := (hB q D' c' hc' n i).2 j _ (hqP j) e1
    have e2 : pull _ (spMap (Polynomial.C : D.obj k →+* Polynomial (D.obj k))) _ _ (pull _ (spMap (D.map f).hom) _ _ y) = 0 :=
      (pull_spMap_comp (ZMod q) (D.map f).hom Polynomial.C (tw q i) n y).symm.trans
        ((congrArg (fun g => pull (ZMod q) (spMap g) (tw q i) n y) (sqD f).symm).trans
          ((pull_spMap_comp (ZMod q) Polynomial.C (D'.map f).hom (tw q i) n y).trans hf))
    have e3 := (hH k i n).1 (e2.trans (map_zero _).symm)
    rw [← c.w f, CommRingCat.hom_comp, spMap_comp', pull_comp, e3, map_zero]
  · intro x
    obtain ⟨j, y, rfl⟩ := (hB q D' c' hc' n i).1 x hqc'
    obtain ⟨y', rfl⟩ := (hH j i n).2 y
    refine ⟨pull _ (spMap (c.ι.app j).hom) _ _ y', ?_⟩
    exact (pull_spMap_comp (ZMod q) (c.ι.app j).hom Polynomial.C (tw q i) n y').symm.trans
      ((congrArg (fun g => pull (ZMod q) (spMap g) (tw q i) n y') (sq j).symm).trans
        (pull_spMap_comp (ZMod q) Polynomial.C (c'.ι.app j).hom (tw q i) n y'))

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLevelGroupAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_level_group_action : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (T : Over S) (l : D.La → (T ⟶ o.A)) (g : LevGrp D w0 r), IsEtLevOver o w0 r l → IsEtLevOver o w0 r (fun y => l (levAct g y)) := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.isEtLevOver_levAct) | (exact GlobalTheory.UPel.HT.EtLev.isEtLevOver_levAct) | (intros; apply GlobalTheory.UPel.HT.EtLev.isEtLevOver_levAct <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLevelKernelUniversal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_level_kernel_universal : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (K : Over S) (κ : K ⟶ o.A), IsFinite K.hom → Etale K.hom → (∀ c ∈ w0 ^ r, κ ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ K, y ≫ κ = x) → ∃ (Z : Over S) (et : D.La → (Z ⟶ o.A)), IsFinite Z.hom ∧ Etale Z.hom ∧ (∀ x y, et (x + y) = et x * et y) ∧ (∀ (c : D.O) x, et (c • x) = et x ≫ o.act.act c) ∧ (∀ x ∈ wSub D w0 r, et x = 1) ∧ ∀ (T : Over S) (l : D.La → (T ⟶ o.A)), (∀ x y, l (x + y) = l x * l y) → (∀ (c : D.O) x, l (c • x) = l x ≫ o.act.act c) → (∀ x ∈ wSub D w0 r, l x = 1) → ∃! h : T ⟶ Z, ∀ y, h ≫ et y = l y := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.exists_finiteEtale_linTorsHom) | (exact GlobalTheory.UPel.HT.EtLev.exists_finiteEtale_linTorsHom) | (intros; apply GlobalTheory.UPel.HT.EtLev.exists_finiteEtale_linTorsHom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLeviNonnegOfChartPlurisubharmonic
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem etale_leviNonneg : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ φ : Y → ℝ, (∀ x ∈ U, ∃ i, x ∈ (A.chart i).source ∧ ContDiffAt ℝ ∞ (φ ∘ (A.chart i).symm) (A.chart i x) ∧ ∀ ξ : Fin n → ℂ, 0 ≤ A.leviAt i φ x ξ) → LeviNonneg n (fun y : U => z y) (fun y : U => φ y) := by
  intro n Y _ _ _ _ _ ι La _ A U z hE φ hφ
  unfold LeviNonneg
  intro x ξ
  have hloc := _root_.GlobalTheory.OTY.etale_isLocalHomeomorph n Y ι La A U z hE
  obtain ⟨e, he, hx⟩ := exists_chart n (fun y : U => z y) hloc x
  obtain ⟨i, hxi, hsm, hpos⟩ := hφ x.1 x.2
  have hzx : z x = e x := he hx
  have hv : e x ∈ e.target := e.map_source hx
  have hsx : e.symm (e x) = x := e.left_inv hx
  obtain ⟨hG, hev, -⟩ := _root_.GlobalTheory.OTY.etale_local_inverse n Y ι La A U z hE e he (e x) hv i (by rw [hsx]; exact hxi)
  rw [levi_eq_leviV n _ e he _ x hx ξ]
  show 0 ≤ (leviV n (fun y => ((φ (e.symm y : Y) : ℝ) : ℂ)) (z x) ξ).re
  rw [hzx]

  have heq : (fun y => ((φ (e.symm y : Y) : ℝ) : ℂ)) =ᶠ[𝓝 (e x)]
      (fun w => ((φ ((A.chart i).symm w) : ℝ) : ℂ)) ∘ (fun v' => A.chart i (e.symm v' : Y)) := by
    filter_upwards [hev] with v' hv'
    simp only [Function.comp_apply, (A.chart i).left_inv hv']
  have hcongr : leviV n (fun y => ((φ (e.symm y : Y) : ℝ) : ℂ)) (e x) ξ =
      leviV n ((fun w => ((φ ((A.chart i).symm w) : ℝ) : ℂ)) ∘
        (fun v' => A.chart i (e.symm v' : Y))) (e x) ξ := by
    unfold leviV
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    congr 2
    apply wd_congr
    filter_upwards [heq.eventuallyEq_nhds] with y hy
    exact ReciprocityTheory.L2DbarEstimates.wdb_congr hy
  have hU : ContDiffAt ℝ 2 (fun w => ((φ ((A.chart i).symm w) : ℝ) : ℂ))
      ((fun v' => A.chart i (e.symm v' : Y)) (e x)) := by
    simp only [hsx]
    exact ((Complex.ofRealCLM.contDiff.contDiffAt).comp _ hsm).of_le (WithTop.coe_le_coe.mpr le_top)
  rw [hcongr, flA_leviV_comp hU (hG.of_le (WithTop.coe_le_coe.mpr le_top)) ξ]
  simp only [hsx]
  exact hpos _

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleTorsionSubgroupUniversal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_torsion_subgroup_universal : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r r' : ℕ), r ≤ r' → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (H : Over S) (i : H ⟶ o.A), IsFinite H.hom → Etale H.hom → (∀ c ∈ w0 ^ r', i ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r', x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ H, y ≫ i = x) → ∃ (K : Over S) (κ : K ⟶ o.A), IsFinite K.hom ∧ Etale K.hom ∧ (∀ c ∈ w0 ^ r, κ ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) ∧ ∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ K, y ≫ κ = x := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.exists_rep_pow_of_le) | (exact GlobalTheory.UPel.HT.EtLev.exists_rep_pow_of_le) | (intros; apply GlobalTheory.UPel.HT.EtLev.exists_rep_pow_of_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvSubstNatMultiplePrimePowConstant
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem pullTwo_mulBy_pow_self {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O) (n : ℕ)
    (t : G.A n ⊗[O] G.A n) :
    pullbackTwo (mulBy O (G.A n) (p ^ n)) t = algebraMap O _
      (Algebra.TensorProduct.lift (Bialgebra.counitAlgHom O (G.A n))
        (Bialgebra.counitAlgHom O (G.A n)) (fun _ _ => Commute.all _ _) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
  | tmul a b =>
    have h : pullbackTwo (mulBy O (G.A n) (p ^ n)) (a ⊗ₜ[O] b) =
        mulBy O (G.A n) (p ^ n) a ⊗ₜ[O] mulBy O (G.A n) (p ^ n) b := rfl
    rw [h, G.mulBy_pow_self, G.mulBy_pow_self, Algebra.TensorProduct.lift_tmul,
      Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul_smul, Algebra.TensorProduct.one_def]

theorem Chart.ev_nmul_pow : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ n, (∀ f, c.ev n (subst (nmul c.μ (p ^ n)) f) = algebraMap O _ (constantCoeff f)) ∧ (∀ s, c.ev₂ n (pull2 (nmul c.μ (p ^ n)) s) = algebraMap O _ (constantCoeff s)) ∧ ∀ f, c.ev (n + 1) (subst (nmul c.μ p) f) = G.mulP n (c.ev n f) := by
  intro p O _ _ G d c n
  refine ⟨fun f => ?_, fun s => ?_, fun f => ?_⟩
  · rw [(GlobalTheory.T.formalChart_natMultiple_eval_properties p O G d c n (p ^ n)).2.1, G.mulBy_pow_self,
      ((GlobalTheory.T.ev_res_counit_compat p O G d c n).1 f).2]
  · rw [(GlobalTheory.T.formalChart_natMultiple_eval_properties p O G d c n (p ^ n)).2.2, pullTwo_mulBy_pow_self,
      (GlobalTheory.T.ev_res_counit_compat p O G d c n).2]
  · rw [(GlobalTheory.T.formalChart_natMultiple_eval_properties p O G d c (n + 1) p).2.1, ← ((GlobalTheory.T.ev_res_counit_compat p O G d c n).1 f).1, mulP_res]

end GlobalTheory.QLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesOfIsConnectedStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coordinates_of_isConnected : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ G : PDivGroup p O, IsConn G → ∃ (d : ℕ) (x : ∀ n, Fin d → G.A n) (ev : ∀ n, MvPowerSeries (Fin d) O →ₐ[O] G.A n), (∀ n i, ∃ N : ℕ, (p : G.A n) ∣ x n i ^ N) ∧ (∀ n, IsEval p (x n) (ev n)) ∧ (∀ n i, G.res n (x (n + 1) i) = x n i) ∧ (∀ n i, Coalgebra.counit (R := O) (x n i) = 0) ∧ (∀ n, Function.Surjective (ev n)) ∧ ∀ m N : ℕ, ∃ n, ∀ f, ev n f = 0 → ∀ α : Fin d →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f := by
  first | exact @GlobalTheory.PDivGroup.exists_coords_of_isConn | exact GlobalTheory.PDivGroup.exists_coords_of_isConn | (intros; apply GlobalTheory.PDivGroup.exists_coords_of_isConn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPairingEqStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_pairing_eq_alt : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (Q : Type) [CommGroup Q] (act : D.O → Q → Q) (r : ℕ) (W : Q → Q → kˣ) (ζ : kˣ), IsPrimitiveRoot ζ (p ^ r) → (∀ a a' b : Q, a ^ (p ^ r) = 1 → a' ^ (p ^ r) = 1 → b ^ (p ^ r) = 1 → W (a * a') b = W a b * W a' b) → (∀ a b : Q, a ^ (p ^ r) = 1 → b ^ (p ^ r) = 1 → W a b * W b a = 1) → (∀ (c : D.O) (a b : Q), a ^ (p ^ r) = 1 → b ^ (p ^ r) = 1 → W (act c a) b = W a (act (D.star c).unop b)) → (∀ a : Q, a ^ (p ^ r) = 1 → (∀ b : Q, b ^ (p ^ r) = 1 → W a b = 1) → a = 1) → ∀ f : D.La → Q, ((∀ x y, f (x + y) = f x * f y) ∧ (∀ (c : D.O) x, f (c • x) = act c (f x)) ∧ (∀ x, f x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, f x = g)) → ∃ f' : D.La → Q, ((∀ x y, f' (x + y) = f' x * f' y) ∧ (∀ (c : D.O) x, f' (c • x) = act c (f' x)) ∧ (∀ x, f' x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, f' x = g)) ∧ ∀ x y, W (f' x) (f' y) = ζ ^ D.EF x y := by
  first | (exact @GlobalTheory.UPel.HT.FinLevSim.exists_level_pairing_eq) | (exact GlobalTheory.UPel.HT.FinLevSim.exists_level_pairing_eq) | (intros; apply GlobalTheory.UPel.HT.FinLevSim.exists_level_pairing_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianShFactorStatement
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_noetherian_sh_factorization : ∀ (R A : Type) [CommRing R] [IsNoetherianRing R] [CommRing A], SH A → ∀ b : R →+* A, ∃ (C : Type) (_ : CommRing C), IsNoetherianRing C ∧ SH C ∧ ∃ (f : R →+* C) (g : C →+* A), g.comp f = b := by
  first | (exact @GlobalTheory.NoethSHFactor.exists_noetherian_sh_factor) | (exact GlobalTheory.NoethSHFactor.exists_noetherian_sh_factor) | (intros; apply GlobalTheory.NoethSHFactor.exists_noetherian_sh_factor  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulEqRegularValueBasicOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ClearDen

theorem exists_pow_mul_eq_val : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (U : A.left.Opens), IsAffineOpen U → ∀ (r : Γ(A.left, U)) (k : (Fin g → ℂ) → ℂ), IsReg u.ex (A.left.basicOpen r) k → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ b : Γ(A.left, U), ∀ z ∈ pre u.ex (A.left.basicOpen r), val u.ex U b z = val u.ex U r z ^ N * k z := by
  intro A _ g L u U hU r k ⟨f, hf⟩
  have hloc := hU.isLocalization_basicOpen r
  obtain ⟨⟨b₀, ⟨_, n, rfl⟩⟩, hb⟩ := IsLocalization.surj (Submonoid.powers r) f
  simp only at hb
  refine ⟨n, fun N hN => ⟨r ^ (N - n) * b₀, fun z hz => ?_⟩⟩
  have hzU : ⊤ ≤ (u.ex z).left ⁻¹ᵁ U := GlobalTheory.top_le_preimage_mono _ (A.left.basicOpen_le r) hz
  have key : ∀ c : Γ(A.left, U), val u.ex (A.left.basicOpen r) (algebraMap Γ(A.left, U) Γ(A.left, A.left.basicOpen r) c) z = val u.ex U c z := by
    intro c
    exact GlobalTheory.valAt'_map _ (homOfLE (A.left.basicOpen_le r)).op c hz
  have e0 := congrArg (fun y => val u.ex (A.left.basicOpen r) y z) hb
  have e1 : val u.ex (A.left.basicOpen r) f z * val u.ex U r z ^ n = val u.ex U b₀ z := by
    rw [← key b₀, ← e0]
    unfold val
    rw [GlobalTheory.valAt'_mul]
    congr 1
    have := key (r ^ n)
    unfold val at this
    rw [this, GlobalTheory.valAt'_pow _ hzU]
  have e2 : val u.ex U (r ^ (N - n) * b₀) z = val u.ex U r z ^ (N - n) * val u.ex U b₀ z := by
    unfold val
    rw [GlobalTheory.valAt'_mul, GlobalTheory.valAt'_pow _ hzU]
  rw [e2, ← e1, hf z hz, ← Nat.sub_add_cancel hN, pow_add, Nat.add_sub_cancel]
  ring

end GlobalTheory.ClearDen
end

