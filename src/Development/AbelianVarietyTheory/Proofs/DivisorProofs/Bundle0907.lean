module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0874
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleDescentDegreeZero
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex Simplicial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.EtC.DescZero

variable {R : Type} [CommRing R]

end GlobalTheory.EtC.DescZero

namespace GlobalTheory.EtC.DescZero

end GlobalTheory.EtC.DescZero

namespace GlobalTheory.EtC.DescZero

def cπ {Y X : Scheme.{0}} (f : Y ⟶ X) (n : ℕ) (k : Fin (n + 1)) : (cech f).obj (op ⦋n⦌) ⟶ (sch.obj Y).obj (op ⦋0⦌) :=
  WidePullback.π (fun _ : Fin (n + 1) => yoneda.map f) k

end GlobalTheory.EtC.DescZero

namespace GlobalTheory.EtC.DescZero

open CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma spec_map_surjective_of_integral_ker_le_nilradical (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A']
    [Algebra.IsIntegral A A'] (hker : RingHom.ker (algebraMap A A') ≤ nilradical A) :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap A A'))) := by
  constructor
  intro x
  let p : PrimeSpectrum A := x
  obtain ⟨Q, -, hQ, hQx⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal (⊥ : Ideal A')
    (by rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot]; exact hker.trans (nilradical_le_prime _))
  exact ⟨(⟨Q, hQ⟩ : PrimeSpectrum A'), PrimeSpectrum.ext hQx⟩

open CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma sec_res_comp_divisor {R : Type} [CommRing R] {F : _root_.GlobalTheory.EtC.Shv R} {W V U : Scheme}
    (h : W ⟶ V) (g : V ⟶ U) (s : _root_.GlobalTheory.EtC.Sec F U) :
    _root_.GlobalTheory.EtC.Sec.res (h ≫ g) s =
      _root_.GlobalTheory.EtC.Sec.res h (_root_.GlobalTheory.EtC.Sec.res g s) := by
  simp [_root_.GlobalTheory.EtC.Sec.res]

open CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma disc_face_eq_id (P : _root_.GlobalTheory.EtC.PSh) (n : ℕ) (i : Fin (n + 2)) :
    SimplicialObject.δ (_root_.GlobalTheory.EtC.disc.obj P) i = 𝟙 _ := by
  first | rfl | simp [SimplicialObject.δ, _root_.GlobalTheory.EtC.disc]

open CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma cobd_eq_zero_of_scheme {R : Type} [CommRing R] {F : _root_.GlobalTheory.EtC.Shv R} (X : Scheme)
    (t : (_root_.GlobalTheory.EtC.free R).obj ((_root_.GlobalTheory.EtC.sch.obj X) _⦋0⦌) ⟶ F) :
    _root_.GlobalTheory.EtC.cobd t = 0 := by
  have h : ∀ i : Fin 2, SimplicialObject.δ (_root_.GlobalTheory.EtC.sch.obj X) i = 𝟙 _ :=
    fun i => disc_face_eq_id (yoneda.obj X) 0 i
  unfold _root_.GlobalTheory.EtC.cobd
  simp [Fin.sum_univ_two, h]

open CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma isCls_secClass_of_val_eq_res {R : Type} [CommRing R] (F : _root_.GlobalTheory.EtC.Shv R)
    (X : Scheme) (s : _root_.GlobalTheory.EtC.Sec F X)
    (t : (_root_.GlobalTheory.EtC.free R).obj ((_root_.GlobalTheory.EtC.sch.obj X) _⦋0⦌) ⟶ F)
    (ht : ∀ (U : Scheme) (x : U ⟶ X), _root_.GlobalTheory.EtC.val t U x = _root_.GlobalTheory.EtC.Sec.res x s) :
    _root_.GlobalTheory.EtC.IsCls t (_root_.GlobalTheory.EtC.secClass F s) := by
  obtain ⟨hex, -, -, -, -⟩ :=
    _root_.GlobalTheory.EtC.isCls_basic R F (_root_.GlobalTheory.EtC.sch.obj X) 0
  obtain ⟨x, hx⟩ := hex t (cobd_eq_zero_of_scheme X t)
  suffices hxs : x = _root_.GlobalTheory.EtC.secClass F s by rw [← hxs]; exact hx
  obtain ⟨z, hz, hzv⟩ := hx
  rw [← hz]
  refine ((_root_.GlobalTheory.EtC.secClass_props R F X).1 s z).1 ?_
  have key : ∀ h, (z : Cochain _ _ ((0 : ℕ) : ℤ)).v (-((0 : ℕ) : ℤ)) 0 h =
      (_root_.GlobalTheory.EtC.chainsXIso R (_root_.GlobalTheory.EtC.sch.obj X) 0).hom ≫ t ≫
        _root_.GlobalTheory.EtC.resι R F := by
    intro h
    rw [hzv]
    exact Cochain.single_v _ _ _
  erw [_root_.GlobalTheory.EtC.CupSpec.ev_def, key, Iso.inv_hom_id_assoc]
  have hval := ht X (𝟙 X)
  calc _ = _root_.GlobalTheory.EtC.Sec.map (_root_.GlobalTheory.EtC.resι R F)
        (_root_.GlobalTheory.EtC.val t X (𝟙 X)) := rfl
    _ = _ := by rw [hval]; simp [_root_.GlobalTheory.EtC.Sec.res]

open CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma cobd_eq_zero_of_face_comp_eq {R : Type} [CommRing R] {F : _root_.GlobalTheory.EtC.Shv R}
    {E : _root_.GlobalTheory.EtC.Spc} (T : (_root_.GlobalTheory.EtC.free R).obj (E _⦋0⦌) ⟶ F)
    (h : (_root_.GlobalTheory.EtC.free R).map (SimplicialObject.δ E 0) ≫ T =
      (_root_.GlobalTheory.EtC.free R).map (SimplicialObject.δ E 1) ≫ T) :
    _root_.GlobalTheory.EtC.cobd T = 0 := by
  unfold _root_.GlobalTheory.EtC.cobd
  simp [Fin.sum_univ_two, h]

open CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma cech_face_comp_cπ_eq_cπ_rev {Y X : Scheme.{0}} (f : Y ⟶ X) (i : Fin 2) :
    SimplicialObject.δ (_root_.GlobalTheory.EtC.cech f) i ≫ _root_.GlobalTheory.EtC.DescZero.cπ f 0 0 =
      _root_.GlobalTheory.EtC.DescZero.cπ f 1 i.rev := by
  fin_cases i <;>
  · simp only [_root_.GlobalTheory.EtC.DescZero.cπ, _root_.GlobalTheory.EtC.cech, SimplicialObject.δ, Arrow.cechNerve]
    erw [WidePullback.lift_π]
    rfl

open CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma res_eq_of_tensorSquare_res_eq_lemma_6 {R : Type} [CommRing R] {F : _root_.GlobalTheory.EtC.Shv R}
    (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A']
    (s : _root_.GlobalTheory.EtC.Sec F (Spec (CommRingCat.of A')))
    (hs : _root_.GlobalTheory.EtC.Sec.res
        (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] A').toRingHom)) s =
      _root_.GlobalTheory.EtC.Sec.res
        (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A').toRingHom)) s)
    {U : Scheme} (y₀ y₁ : U ⟶ Spec (CommRingCat.of A'))
    (hy : y₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap A A')) =
      y₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap A A'))) :
    _root_.GlobalTheory.EtC.Sec.res y₀ s = _root_.GlobalTheory.EtC.Sec.res y₁ s := by
  let u := pullback.lift y₀ y₁ hy ≫ (pullbackSpecIso A A' A').hom
  have hu₀ : u ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] A').toRingHom) = y₀ := by
    simp only [u, Category.assoc]
    erw [pullbackSpecIso_hom_fst]
    exact pullback.lift_fst _ _ _
  have hu₁ : u ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A').toRingHom) = y₁ := by
    simp only [u, Category.assoc]
    erw [pullbackSpecIso_hom_snd]
    exact pullback.lift_snd _ _ _
  clear_value u
  rw [← hu₀, ← hu₁, sec_res_comp_divisor, sec_res_comp_divisor, hs]

open CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma cπ_comp_eq_cπ_comp {Y X : Scheme.{0}} (f : Y ⟶ X) (n : ℕ) (k l : Fin (n + 1))
    (U : Scheme.{0}) (e : ((_root_.GlobalTheory.EtC.cech f).obj (op ⦋n⦌)).obj (op U)) :
    (show U ⟶ Y from (_root_.GlobalTheory.EtC.DescZero.cπ f n k).app (op U) e) ≫ f =
      (show U ⟶ Y from (_root_.GlobalTheory.EtC.DescZero.cπ f n l).app (op U) e) ≫ f := by
  have h := (WidePullback.π_arrow (fun _ : Fin (n + 1) => yoneda.map f) k).trans
    (WidePullback.π_arrow (fun _ : Fin (n + 1) => yoneda.map f) l).symm
  exact congr_arg (fun φ => φ.app (op U) e) h

open CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma cechDiag_comp_cπ_eq_id {Y X : Scheme.{0}} (f : Y ⟶ X) :
    (_root_.GlobalTheory.CechOne.cechDiag f).app (op ⦋0⦌) ≫ _root_.GlobalTheory.EtC.DescZero.cπ f 0 0 = 𝟙 _ := by
  simp only [_root_.GlobalTheory.CechOne.cechDiag, _root_.GlobalTheory.EtC.DescZero.cπ]
  erw [WidePullback.lift_π]
  rfl


open CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
theorem _root_.GlobalTheory.EtC.DescZero.desc_zero : ∀ (q : ℕ) [NeZero q] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'],
    Algebra.IsIntegral A A' → RingHom.ker (algebraMap A A') ≤ nilradical A → IsUnit (q : A) →
    ∀ (j : ℤ) (b : _root_.GlobalTheory.EtC.Ht q (_root_.GlobalTheory.EtC.sp A') 0 j),
      _root_.GlobalTheory.EtC.pull _ (_root_.GlobalTheory.EtC.spMap (Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] A').toRingHom) _ 0 b =
        _root_.GlobalTheory.EtC.pull _ (_root_.GlobalTheory.EtC.spMap (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A').toRingHom) _ 0 b →
      ∃ a : _root_.GlobalTheory.EtC.Ht q (_root_.GlobalTheory.EtC.sp A) 0 j, _root_.GlobalTheory.EtC.pull _ (_root_.GlobalTheory.EtC.spMap (algebraMap A A')) _ 0 a = b := by
  intro q _ A A' _ _ _ hint hker hq j b hb
  let f : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A A'))
  haveI : IsIntegralHom f := by rw [IsIntegralHom.SpecMap_iff]; exact hint.isIntegral
  haveI : Surjective f := spec_map_surjective_of_integral_ker_le_nilradical A A' hker
  have hbij : Function.Bijective
      (_root_.GlobalTheory.EtC.pull (ZMod q) (_root_.GlobalTheory.EtC.cechAug f) (_root_.GlobalTheory.EtC.tw q j) 0) :=
    _root_.GlobalTheory.EtC.b4 q f
      (by simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) j 0
  set F := _root_.GlobalTheory.EtC.tw q j with hF
  obtain ⟨-, hbijc, -, hres, -⟩ := _root_.GlobalTheory.EtC.secClass_props (ZMod q) F (Spec (CommRingCat.of A'))
  obtain ⟨s, rfl⟩ := hbijc.2 b
  have hs : _root_.GlobalTheory.EtC.Sec.res
        (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] A').toRingHom)) s =
      _root_.GlobalTheory.EtC.Sec.res
        (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A').toRingHom)) s := by
    apply (_root_.GlobalTheory.EtC.secClass_props (ZMod q) F _).2.1.1
    rw [← hres, ← hres]
    exact hb
  have hfreeY := _root_.GlobalTheory.EtC.FreeHom.main (ZMod q)
    ((_root_.GlobalTheory.EtC.sch.obj (Spec (CommRingCat.of A'))) _⦋0⦌) F
  obtain ⟨t, ht⟩ := hfreeY.2.1
    (fun U x => _root_.GlobalTheory.EtC.Sec.res (show U ⟶ Spec (CommRingCat.of A') from x) s)
    (fun V U g x => sec_res_comp_divisor g (show U ⟶ Spec (CommRingCat.of A') from x) s)
  have hrep := isCls_secClass_of_val_eq_res F _ s t ht
  obtain ⟨hex, -, -, -, hpull⟩ :=
    _root_.GlobalTheory.EtC.isCls_basic (ZMod q) F (_root_.GlobalTheory.EtC.cech f) 0
  obtain ⟨T, hTdef⟩ : ∃ T, T =
      (_root_.GlobalTheory.EtC.free (ZMod q)).map (_root_.GlobalTheory.EtC.DescZero.cπ f 0 0) ≫ t :=
    ⟨_, rfl⟩
  have hT : _root_.GlobalTheory.EtC.cobd T = 0 := by
    refine cobd_eq_zero_of_face_comp_eq T ?_
    have hfree := _root_.GlobalTheory.EtC.FreeHom.main (ZMod q)
      ((_root_.GlobalTheory.EtC.cech f) _⦋1⦌) F
    apply hfree.1
    intro U e
    simp only [hTdef, ← Functor.map_comp_assoc, cech_face_comp_cπ_eq_cπ_rev]
    rw [hfreeY.2.2.2.1, hfreeY.2.2.2.1, ht, ht]
    exact res_eq_of_tensorSquare_res_eq_lemma_6 A A' s hs _ _
      (cπ_comp_eq_cπ_comp f 1 (Fin.rev 0) (Fin.rev 1) U e)
  obtain ⟨x, hx⟩ := hex T hT
  have hcx : _root_.GlobalTheory.EtC.pull (ZMod q) (_root_.GlobalTheory.CechOne.cechDiag f) F 0 x =
      _root_.GlobalTheory.EtC.secClass F s := by
    refine (_root_.GlobalTheory.EtC.isCls_basic (ZMod q) F
      (_root_.GlobalTheory.EtC.sch.obj (Spec (CommRingCat.of A'))) 0).2.2.1 t _ _ ?_ hrep
    have h := hpull _ (_root_.GlobalTheory.CechOne.cechDiag f) T x hx
    have hcomp : (_root_.GlobalTheory.EtC.free (ZMod q)).map
        ((_root_.GlobalTheory.CechOne.cechDiag f).app (op ⦋0⦌)) ≫ T = t := by
      rw [hTdef, ← Functor.map_comp_assoc]
      erw [cechDiag_comp_cπ_eq_id]
      rw [CategoryTheory.Functor.map_id, Category.id_comp]
    rw [hcomp] at h
    exact h
  obtain ⟨a, ha⟩ := hbij.2 x
  refine ⟨a, ?_⟩
  change _root_.GlobalTheory.EtC.pull (ZMod q) (_root_.GlobalTheory.EtC.sch.map f) F 0 a = _
  rw [← _root_.GlobalTheory.CechOne.cechDiag_aug, _root_.GlobalTheory.EtC.pull_comp, ha, hcx]

end GlobalTheory.EtC.DescZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralTensorPointsSharpStableRing
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

namespace GlobalTheory.OrbFinAf

theorem ratCast_mem_intV_eventually (p : ℕ) [Fact p.Prime] (q : ℚ) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      algebraMap ℚ (Qv v) q ∈ v.1.adicCompletionIntegers ℚ := by
  have h : ∀ᶠ w in (Filter.cofinite : Filter (HeightOneSpectrum ℤ)),
      algebraMap ℚ (w.adicCompletion ℚ) q ∈ w.adicCompletionIntegers ℚ :=
    (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q).2.mono fun _ hv => hv
  exact (Subtype.val_injective.tendsto_cofinite).eventually h

variable {p : ℕ} [Fact p.Prime]

theorem basV_repr_tmul (G : HTGroup p) (v : AwayP p) (r : Qv v) (c : G.C) (k : Fin (Module.finrank ℚ G.C)) :
    (basV G v).repr (r ⊗ₜ c) k = r * algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr c k) := by
  simp [basV, Algebra.TensorProduct.basis_repr_tmul]

theorem eq_sum_tmul (G : HTGroup p) (v : AwayP p) (y : Qv v ⊗[ℚ] G.C) :
    y = ∑ i, (basV G v).repr y i ⊗ₜ (Module.finBasis ℚ G.C i) := by
  conv_lhs => rw [← (basV G v).sum_repr y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [basV, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem isIntV_of_eq_sum (G : HTGroup p) (v : AwayP p) {ι : Type*} (s : Finset ι) (r : ι → Qv v) (c : ι → G.C)
    (hr : ∀ i ∈ s, r i ∈ v.1.adicCompletionIntegers ℚ)
    (hc : ∀ i ∈ s, ∀ k, algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr (c i) k) ∈ v.1.adicCompletionIntegers ℚ) :
    IsIntV G v (∑ i ∈ s, r i ⊗ₜ c i) := by
  intro k
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  exact sum_mem fun i hi => by rw [basV_repr_tmul]; exact mul_mem (hr i hi) (hc i hi k)

theorem intV_order_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), IsIntV G v 1 ∧ (∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) ∧ (∀ y : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v (starT G.star (Qv v) y).unop) := by
  intro p _ G
  set b := Module.finBasis ℚ G.C
  have H := ((Filter.eventually_all.2 fun k => ratCast_mem_intV_eventually p (b.repr 1 k)).and
    (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun k =>
      ratCast_mem_intV_eventually p (b.repr (b i * b j) k))).and
    (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun k =>
      ratCast_mem_intV_eventually p (b.repr (G.star (b i)).unop k))
  refine H.mono fun v ⟨⟨h1, hm⟩, hs⟩ => ⟨?_, ?_, ?_⟩
  · intro k
    rw [Algebra.TensorProduct.one_def, basV_repr_tmul, one_mul]
    exact h1 k
  · intro y z hy hz
    have e : y * z = ∑ ij : Fin (Module.finrank ℚ G.C) × Fin (Module.finrank ℚ G.C),
        ((basV G v).repr y ij.1 * (basV G v).repr z ij.2) ⊗ₜ (b ij.1 * b ij.2) := by
      conv_lhs => rw [eq_sum_tmul G v y, eq_sum_tmul G v z]
      rw [Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
      simp only [Algebra.TensorProduct.tmul_mul_tmul]
      rfl
    rw [e]
    exact isIntV_of_eq_sum G v _ _ _ (fun ij _ => mul_mem (hy ij.1) (hz ij.2)) (fun ij _ k => hm ij.1 ij.2 k)
  · intro y hy
    have e : (starT G.star (Qv v) y).unop = ∑ i, (basV G v).repr y i ⊗ₜ (G.star (b i)).unop := by
      conv_lhs => rw [eq_sum_tmul G v y]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← MulOpposite.opAddEquiv_symm_apply, map_sum]
      exact Finset.sum_congr rfl fun i _ => starT_tmul G.star (Qv v) _ _
    rw [e]
    exact isIntV_of_eq_sum G v _ _ _ (fun i _ => hy i) (fun i _ k => hs i k)

end GlobalTheory.OrbFinAf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralUnitaryPointsAtPlaceMulMem
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

open scoped RestrictedProduct

namespace GlobalTheory.OrbFinAf

section General

variable {C : Type} [Ring C] [Algebra ℚ C] {ι : Type} [Fintype ι] (b : Module.Basis ι ℚ C)
  {R : Type} [CommRing R] [Algebra ℚ R] (S : Subring R)

theorem repr_mul_mem (hc : ∀ i j k, algebraMap ℚ R (b.repr (b i * b j) k) ∈ S)
    {y y' : R ⊗[ℚ] C} (hy : ∀ i, (Algebra.TensorProduct.basis R b).repr y i ∈ S)
    (hy' : ∀ i, (Algebra.TensorProduct.basis R b).repr y' i ∈ S) (k : ι) :
    (Algebra.TensorProduct.basis R b).repr (y * y') k ∈ S := by
  set B := Algebra.TensorProduct.basis R b
  have hB : ∀ i j, B.repr (B i * B j) k = algebraMap ℚ R (b.repr (b i * b j) k) := by
    intro i j
    simp [B, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.basis_repr_tmul]
  rw [← B.sum_repr y, ← B.sum_repr y', Finset.sum_mul_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [smul_mul_smul_comm, map_sum, map_smul, Finset.sum_apply',
    Finsupp.smul_apply, smul_eq_mul, hB]
  exact S.sum_mem fun i _ => S.sum_mem fun j _ => S.mul_mem (S.mul_mem (hy i) (hy' j)) (hc i j k)

end General

theorem eventually_rat_mem (p : ℕ) [Fact p.Prime] (q : ℚ) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      algebraMap ℚ (Qv v) q ∈ v.1.adicCompletionIntegers ℚ := by
  have h := (show Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ] from
    algebraMap ℚ (AfP p) q).2
  filter_upwards [h] with v hv
  have e : (AfP.eval v) (algebraMap ℚ (AfP p) q) = algebraMap ℚ (Qv v) q := (AfP.eval v).commutes q
  rw [← e]
  exact hv

theorem mul_mem_IntV_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p),
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a ∈ IntV G v, ∀ b ∈ IntV G v, a * b ∈ IntV G v := by
  intro p _ G
  have hall : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ i j k,
      algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr
        (Module.finBasis ℚ G.C i * Module.finBasis ℚ G.C j) k) ∈ v.1.adicCompletionIntegers ℚ := by
    simp only [Filter.eventually_all]
    intro i j k
    exact eventually_rat_mem p _
  filter_upwards [hall] with v hv
  intro a ha a' ha'
  obtain ⟨h1, h2, h3, h4⟩ := ha
  obtain ⟨h1', h2', h3', h4'⟩ := ha'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    have := repr_mul_mem (Module.finBasis ℚ G.C) (v.1.adicCompletionIntegers ℚ).toSubring hv h1 h1' k
    simpa [IsIntV, basV] using this
  · intro k
    have := repr_mul_mem (Module.finBasis ℚ G.C) (v.1.adicCompletionIntegers ℚ).toSubring hv h2' h2 k
    simpa [IsIntV, basV, _root_.mul_inv_rev] using this
  · have := (v.1.adicCompletionIntegers ℚ).mul_mem _ _ h3 h3'
    simpa using this
  · have := (v.1.adicCompletionIntegers ℚ).mul_mem _ _ h4' h4
    simpa [_root_.mul_inv_rev] using this

end GlobalTheory.OrbFinAf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIsIntegralInCompletedTensorBasisMulExp
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

theorem basV_repr_mul (G : HTGroup p) (v : AwayP p) (a b : Qv v ⊗[ℚ] G.C) (k : Fin (Module.finrank ℚ G.C)) :
    (basV G v).repr (a * b) k = ∑ i, ∑ j, (basV G v).repr a i * (basV G v).repr b j *
      algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr
        (Module.finBasis ℚ G.C i * Module.finBasis ℚ G.C j) k) := by
  conv_lhs => rw [← (basV G v).sum_repr a, ← (basV G v).sum_repr b]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul, map_sum, map_smul, Finset.sum_apply',
    Finsupp.smul_apply, smul_eq_mul, basV, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.basis_repr_tmul,
    Finsupp.mapRange_apply]
  rw [Finset.sum_comm]


omit [Fact p.Prime] in
theorem eventually_rat_mem_integers (q : ℚ) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      algebraMap ℚ (Qv v) q ∈ v.1.adicCompletionIntegers ℚ := by
  have h : ∀ᶠ w in (Filter.cofinite : Filter (HeightOneSpectrum ℤ)),
      algebraMap ℚ (w.adicCompletion ℚ) q ∈ w.adicCompletionIntegers ℚ :=
    (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q).2
  exact Subtype.val_injective.tendsto_cofinite.eventually h

theorem isIntV_mul_eventually (G : HTGroup p) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a b : Qv v ⊗[ℚ] G.C,
      IsIntV G v a → IsIntV G v b → IsIntV G v (a * b) := by
  have h : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ i j k : Fin (Module.finrank ℚ G.C),
      algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr
        (Module.finBasis ℚ G.C i * Module.finBasis ℚ G.C j) k) ∈ v.1.adicCompletionIntegers ℚ := by
    simp only [Filter.eventually_all]
    intro i j k
    exact eventually_rat_mem_integers _
  filter_upwards [h] with v hv a b ha hb k
  rw [basV_repr_mul]
  exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ =>
    Subring.mul_mem _ (Subring.mul_mem _ (ha i) (hb j)) (hv i j k)

theorem isIntV_mul_eventually' : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p),
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a b : Qv v ⊗[ℚ] G.C,
      IsIntV G v a → IsIntV G v b → IsIntV G v (a * b) :=
  fun _ _ G => isIntV_mul_eventually G

end GlobalTheory.OrbFinAf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSideOfModels
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicSide

theorem adForms_eq_of_reps {Gr Γ : Type} [Group Gr] [Group Γ] (ι : Γ →* Gr) {Wc : Type} [NormedAddCommGroup Wc]
    [InnerProductSpace ℂ Wc] (ρ : Γ →* Module.End ℂ Wc) {J J' : Subgroup Gr} (χ : J →* ℂˣ) (hle : J' ≤ J) {I : Type}
    {y : I → Gr} (hy : Bridge.IsReps ι J' y) {f f' : Gr → Wc} (h1 : f ∈ Bridge.AdForms ι ρ J χ)
    (h2 : f' ∈ Bridge.AdForms ι ρ J χ) (h : ∀ k, f (y k) = f' (y k)) : f = f' := by
  funext g
  obtain ⟨k, ⟨γ, u, rfl⟩, -⟩ := hy g
  have m1 := h1 γ (y k) ⟨u, hle u.2⟩
  have m2 := h2 γ (y k) ⟨u, hle u.2⟩
  rw [h k] at m1
  exact m1.trans m2.symm


set_option maxHeartbeats 1000000 in
theorem exists_thAd_of_models : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → ∀ (i : Fin D.R.m) (t : T0) (K' : Type) [Field K'] (σ' : K' →+* ℂ) (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W) (Cl : Type) (h : Cl → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))), J' ≤ levJ R i t → Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => FWT.fin _ (h k)) → ∀ v₀ : (R.MW i (sg0 D A)).Vec, ∃ thAd, ThAdIs R i t h c0' v₀ thAd := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hR i t K' _ σ' c0' Cl h J' hle hr v₀
  classical
  obtain ⟨hinj, hrange, -⟩ := hR.HV i t
  have huniq : ∀ y y' x, Place R i t h c0' y x → Place R i t h c0' y' x → y = y' := fun y y' x h1 h2 =>
    hinj (adForms_eq_of_reps _ _ _ hle hr (hrange.le (LinearMap.mem_range_self _ y))
      (hrange.le (LinearMap.mem_range_self _ y')) fun k => (h1 k).trans (h2 k).symm)
  refine ⟨fun x => if hx : ∃ y, Place R i t h c0' y x then onQ (Wc D i) (R.thF i t hx.choose v₀) else 0, fun y x hy => ?_⟩
  have hx : ∃ y, Place R i t h c0' y x := ⟨y, hy⟩
  simp only [dif_pos hx]
  rw [huniq _ _ _ hx.choose_spec hy]

end GlobalTheory.AdelicSide
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicUnitCarryingFormToNormMultipleStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicUnit_carrying_form_to_normMultiple : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.C) (M : Type) [Field M] [NumberField M] (j : M →+* G.C) (σ : M →+* M), (∀ y : M, β * sh G (j y) = j (σ y) * β) → ∀ (a : M) (u : (AfP p ⊗[ℚ] M)ˣ), (u : AfP p ⊗[ℚ] M) * Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom u = 1 ⊗ₜ a → ∃ U : (AfP p ⊗[ℚ] G.C)ˣ, (U : AfP p ⊗[ℚ] G.C) * inC G (AfP p) β * (starT G.star (AfP p) U).unop = inC G (AfP p) (j a * β) ∧ ∀ y : G.C, (∀ m : M, y * j m = j m * y) → inC G (AfP p) y * U = U * inC G (AfP p) y := by
  first | (exact @GlobalTheory.adelic_norm_move) | (exact GlobalTheory.adelic_norm_move) | (intros; apply GlobalTheory.adelic_norm_move  <;> assumption)
end

