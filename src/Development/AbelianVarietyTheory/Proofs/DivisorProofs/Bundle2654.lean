module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2583
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2495
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2607
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2535
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2623
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumMultResCycIndicatorSymm
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixHt.CycLoc

theorem length_quot_equiv (R S : Type) [CommRing R] [CommRing S] (e : R ≃+* S) (a : R) :
    Module.length R (R ⧸ Ideal.span {a}) = Module.length S (S ⧸ Ideal.span {e a}) := by
  letI : Algebra R S := e.toRingHom.toAlgebra
  let f : R ≃ₐ[R] S := AlgEquiv.ofRingEquiv (f := e) fun _ => rfl
  rw [← Module.length_eq_of_surjective (S := R) (R := S) (M := S ⧸ Ideal.span {e a}) e.surjective]
  exact (Ideal.quotientEquivAlg (Ideal.span {a}) (Ideal.span {e a}) f (by
    rw [Ideal.map_span, Set.image_singleton]; rfl)).toLinearEquiv.length_eq

theorem finite_height_one (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (a : R) (ha : a ≠ 0) :
    {p : PrimeSpectrum R | p.asIdeal.height = 1 ∧ a ∈ p.asIdeal}.Finite := by
  refine ((Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {a})).preimage
    (f := PrimeSpectrum.asIdeal) fun _ _ _ _ h => PrimeSpectrum.ext h).subset ?_
  rintro p ⟨hp, hap⟩
  refine ⟨⟨p.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hap⟩, fun q hq hqp => ?_⟩
  by_contra hn
  have := hq.1
  have h1 : q < p.asIdeal := lt_of_le_not_ge hqp hn
  have h0 : (⊥ : Ideal R) < q := bot_lt_iff_ne_bot.2 fun h =>
    ha (by simpa [h] using (Ideal.span_singleton_le_iff_mem _).1 hq.2)
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime h1
  have e0 := Ideal.height_add_one_le_of_lt_of_isPrime h0
  rw [hp] at e1
  have : (⊥ : Ideal R).height + 1 + 1 ≤ 1 := (add_le_add_left e0 1).trans e1
  rw [Ideal.height_bot] at this
  exact absurd this (by decide)

theorem stalk_equiv (X : Scheme.{0}) (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    ∃ e : X.presheaf.stalk (X.fromSpecStalk x p) ≃+* Localization.AtPrime p.asIdeal,
      ∀ (U : X.Opens) (hq : X.fromSpecStalk x p ∈ U) (hx : x ∈ U) (s : Γ(X, U)),
        e (X.presheaf.germ U _ hq s) =
          algebraMap (X.presheaf.stalk x) (Localization.AtPrime p.asIdeal) (X.presheaf.germ U x hx s) := by
  let y : Spec (X.presheaf.stalk x) := p
  have := GlobalTheory.LocalRingGeneralisation.isIso_stalkMap_fromSpecStalk X x y
  refine ⟨(asIso ((X.fromSpecStalk x).stalkMap y) ≪≫ Spec.stalkIso _ y).commRingCatIsoToRingEquiv, ?_⟩
  intro U hq hx s
  have h1 := Scheme.Hom.germ_stalkMap_apply (X.fromSpecStalk x) U y hq s
  show (Spec.stalkIso _ y).hom ((X.fromSpecStalk x).stalkMap y ((X.presheaf.germ U _ hq).hom s)) = _
  rw [h1, Scheme.fromSpecStalk_app hx]
  have h2 := congrArg (fun f => f.hom ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv.hom ((X.presheaf.germ U x hx).hom s)))
    (Spec.germ_stalkMapIso_hom (R := X.presheaf.stalk x) (x := y))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom,
    Iso.inv_hom_id, CommRingCat.id_apply] at h2
  refine Eq.trans ?_ h2
  simp only [← CommRingCat.comp_apply, Category.assoc, TopCat.Presheaf.germ_res]
  erw [TopCat.Presheaf.germ_res]

theorem specializes_fromSpecStalk (X : Scheme.{0}) (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    X.fromSpecStalk x p ⤳ x := (Scheme.range_fromSpecStalk (x := x)).le ⟨p, rfl⟩

theorem coheight_fromSpecStalk (X : Scheme.{0}) (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    Order.coheight (X.fromSpecStalk x p) = p.asIdeal.height := by
  obtain ⟨e, -⟩ := stalk_equiv X x p
  have h1 := ringKrullDim_stalk_eq_coheight (X.fromSpecStalk x p)
  rw [ringKrullDim_eq_of_ringEquiv e, IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal] at h1
  exact_mod_cast h1.symm

theorem mem_nonzeroLocus_iff_notMem {X : Scheme.{0}} {A : LB X} (s : A.Sec) {i : A.ι} {x : X} (hi : x ∈ A.U i)
    (p : PrimeSpectrum (X.presheaf.stalk x)) :
    X.fromSpecStalk x p ∈ nonzeroLocus s ↔ X.presheaf.germ _ x hi (s.f i) ∉ p.asIdeal := by
  have hzi : X.fromSpecStalk x p ∈ A.U i := (specializes_fromSpecStalk X x p).mem_open (A.U i).isOpen hi
  obtain ⟨e, he⟩ := stalk_equiv X x p
  rw [Cartier.mem_nonzeroLocus_iff s i hzi, Scheme.mem_basicOpen _ _ _ hzi, ← MulEquiv.isUnit_map e, he _ hzi hi,
    IsLocalization.AtPrime.isUnit_to_map_iff _ p.asIdeal, Ideal.mem_primeCompl_iff]

theorem ker_stalkMap_clo (X : Scheme.{0}) (z : X) (w : clo z) (p : PrimeSpectrum (X.presheaf.stalk (cloι z w)))
    (hp : X.fromSpecStalk (cloι z w) p = z) : RingHom.ker ((cloι z).stalkMap w).hom = p.asIdeal := by
  let g : PrimeSpectrum ((clo z).presheaf.stalk w) := ⟨⊥, Ideal.isPrime_bot⟩
  have hg : (clo z).fromSpecStalk w g = genericPoint (clo z) := by
    have h := coheight_fromSpecStalk (clo z) w g
    rw [show g.asIdeal.height = 0 from Ideal.height_bot, Order.coheight_eq_zero] at h
    exact ((genericPoint_specializes _).antisymm (h (show _ ≤ genericPoint (clo z) from genericPoint_specializes _))).eq.symm
  have h : X.fromSpecStalk (cloι z w) (Spec.map ((cloι z).stalkMap w) g) = cloι z ((clo z).fromSpecStalk w g) :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans ((congrArg (fun f => f g)
      (Scheme.SpecMap_stalkMap_fromSpecStalk (cloι z) (x := w))).trans (Scheme.Hom.comp_apply _ _ _))
  rw [hg, cloι_genericPoint] at h
  have h' := (X.fromSpecStalk (cloι z w)).isEmbedding.injective (h.trans hp.symm)
  exact congrArg PrimeSpectrum.asIdeal h'

theorem germ_secPull {X V : Scheme.{0}} {L : LB X} (s : L.Sec) (b : V ⟶ X) (v : V) (i : L.ι) (hi : b v ∈ L.U i)
    (hv : v ∈ (L.pull b).U fun _ => i) :
    V.presheaf.germ _ v hv ((GlobalTheory.secPull s b).f fun _ => i) = b.stalkMap v (X.presheaf.germ _ _ hi (s.f i)) := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

variable {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}

theorem coheight_one_iff (hq : IsAmb q) {z : Y} (w : clo z) (hz : Order.coheight z = 1) :
    Order.coheight w = 1 ↔ Order.coheight (cloι z w) = 2 := by
  have hB := GlobalTheory.MixHt.hasDim_basic k Y q hq
  obtain ⟨m, hm⟩ := hB.1
  obtain ⟨d, -, hd⟩ := hm (genericPoint Y)
  have hY : topologicalKrullDim Y = d := (hB.2.2.2.2.2 Y d).1 hd
  cases d with
  | zero =>
    obtain ⟨d', -, hd'⟩ := hm z
    have := _root_.GlobalTheory.DimCoheight.coheight_add_eq k Y q hq 0 hY z d' hd'
    rw [hz] at this
    simp at this
  | succ e => exact ((_root_.GlobalTheory.MixHt.dimOne k Y q hq e hY).2 z w hz).2

theorem germ_ne_zero {A : LB Y} {s : A.Sec} (hs : genericPoint Y ∈ nonzeroLocus s) {i : A.ι} {x : Y} (hi : x ∈ A.U i) :
    Y.presheaf.germ _ x hi (s.f i) ≠ 0 := fun h0 =>
  fnOf_sec_ne_zero hs (gen_mem hi) ((algebraMap_germ hi (s.f i)).symm.trans ((congrArg _ h0).trans (map_zero _)))

variable [IsLocallyNoetherian Y]

theorem mult_eq {A : LB Y} (hA : A.IsLB) (s : A.Sec) (hs : genericPoint Y ∈ nonzeroLocus s) {i : A.ι} {x : Y}
    (hi : x ∈ A.U i) (p : PrimeSpectrum (Y.presheaf.stalk x)) (hp : p.asIdeal.height = 1) :
    (divOfSec hA s hs).mult (Y.fromSpecStalk x p) = (Module.length (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⧸ Ideal.span {(algebraMap (Y.presheaf.stalk x) (Localization.AtPrime p.asIdeal)
        (Y.presheaf.germ _ x hi (s.f i)))})).toNat := by
  have hzi : Y.fromSpecStalk x p ∈ A.U i := (specializes_fromSpecStalk Y x p).mem_open (A.U i).isOpen hi
  obtain ⟨e, he⟩ := stalk_equiv Y x p
  rw [mult_divOfSec ((coheight_fromSpecStalk Y x p).trans hp) hzi, length_quot_equiv _ _ e, he _ hzi hi]

theorem resCyc_eq (hq : IsAmb q) {B : LB Y} (hB : B.IsLB) (t : B.Sec) {j : B.ι} {x : Y} (hj : x ∈ B.U j)
    (hx : Order.coheight x = 2) (p : PrimeSpectrum (Y.presheaf.stalk x)) (hp : p.asIdeal.height = 1)
    (ht : Y.presheaf.germ _ x hj (t.f j) ∉ p.asIdeal) {z : Y} (hz : Y.fromSpecStalk x p = z) :
    resCyc hB t (Set.indicator {x} 1) z = (Module.length (Y.presheaf.stalk x ⧸ p.asIdeal)
      ((Y.presheaf.stalk x ⧸ p.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk p.asIdeal (Y.presheaf.germ _ x hj (t.f j))})).toNat := by
  have hzx : z ⤳ x := hz ▸ specializes_fromSpecStalk Y x p
  have hz1 : Order.coheight z = 1 := hz ▸ (coheight_fromSpecStalk Y x p).trans hp
  have hzt : z ∈ nonzeroLocus t := hz ▸ (mem_nonzeroLocus_iff_notMem t hj p).2 ht
  obtain ⟨w, rfl⟩ : x ∈ Set.range (cloι z) :=
    hzx.mem_closed (cloι z).isClosedEmbedding.isClosed_range ⟨_, cloι_genericPoint z⟩
  have h : genericPoint (clo z) ∈ nonzeroLocus (GlobalTheory.secPull t (cloι z)) := by
    rw [GlobalTheory.nonzeroLocus_secPull]
    show cloι z (genericPoint (clo z)) ∈ nonzeroLocus t
    rwa [cloι_genericPoint]
  have hw : w ∈ (B.pull (cloι z)).U fun _ => j := Set.mem_iInter.2 fun _ => hj
  have hk := ker_stalkMap_clo Y z w p hz
  let e : (Y.presheaf.stalk (cloι z w) ⧸ p.asIdeal) ≃+* (clo z).presheaf.stalk w :=
    (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective ((cloι z).stalkMap_surjective w))
  rw [resCyc, dite_eq_left h, finsum_eq_single _ w fun w' hw' => by
    rw [Set.indicator_of_notMem (s := {cloι z w}) (a := cloι z w')
      (fun e => hw' ((cloι z).isClosedEmbedding.injective (Set.mem_singleton_iff.1 e))), mul_zero],
    Set.indicator_of_mem (Set.mem_singleton _), Pi.one_apply, mul_one,
    mult_divOfSec ((coheight_one_iff hq w hz1).2 hx) hw, germ_secPull t _ w j hj, length_quot_equiv _ _ e, Int.cast_natCast]
  rfl

theorem of_term_ne_zero (hq : IsAmb q) {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (s : A.Sec) (t : B.Sec)
    (hs : genericPoint Y ∈ nonzeroLocus s) {x z : Y}
    (h : ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t (Set.indicator {x} 1) z ≠ 0) :
    Order.coheight x = 2 ∧ Order.coheight z = 1 ∧ z ∉ nonzeroLocus s ∧ z ⤳ x := by
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
  have h1' : (divOfSec hA s hs).mult z ≠ 0 := by exact_mod_cast h1
  have hz := CartierDiv.coheight_eq_one_of_mult_ne_zero h1'
  rw [resCyc] at h2
  split_ifs at h2 with h3
  · obtain ⟨w, hw⟩ := not_forall.1 (mt finsum_eq_zero_of_forall_eq_zero h2)
    obtain ⟨h4, h5⟩ := mul_ne_zero_iff.1 hw
    have h6 : cloι z w = x := Set.mem_singleton_iff.1 (Set.mem_of_indicator_ne_zero h5)
    have h7 := CartierDiv.coheight_eq_one_of_mult_ne_zero (Int.cast_ne_zero.1 h4)
    refine ⟨h6 ▸ (coheight_one_iff hq w hz).1 h7, hz,
      fun h => notMem_supp_divOfSec.2 h (CartierDiv.mem_supp_of_mult_ne_zero h1'), ?_⟩
    have := (genericPoint_specializes w).map (cloι z).continuous
    rwa [cloι_genericPoint, h6] at this
  · exact absurd rfl h2

theorem finsum_eq (hq : IsAmb q) {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (s : A.Sec) (t : B.Sec)
    (hs : genericPoint Y ∈ nonzeroLocus s) {x : Y} {i : A.ι} {j : B.ι} (hi : x ∈ A.U i) (hj : x ∈ B.U j)
    (hx : Order.coheight x = 2) (P : Finset (PrimeSpectrum (Y.presheaf.stalk x)))
    (hP : ∀ p, p ∈ P ↔ p.asIdeal.height = 1 ∧ Y.presheaf.germ _ x hi (s.f i) ∈ p.asIdeal)
    (hb : ∀ p ∈ P, Y.presheaf.germ _ x hj (t.f j) ∉ p.asIdeal) :
    ∑ᶠ z, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t (Set.indicator {x} 1) z =
      ((∑ p ∈ P, (Module.length (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⧸ Ideal.span {(algebraMap (Y.presheaf.stalk x) (Localization.AtPrime p.asIdeal)
          (Y.presheaf.germ _ x hi (s.f i)))})).toNat * (Module.length (Y.presheaf.stalk x ⧸ p.asIdeal)
        ((Y.presheaf.stalk x ⧸ p.asIdeal) ⧸
          Ideal.span {Ideal.Quotient.mk p.asIdeal (Y.presheaf.germ _ x hj (t.f j))})).toNat : ℕ) : ℝ) := by
  classical
  let ι : PrimeSpectrum (Y.presheaf.stalk x) → Y := fun p => Y.fromSpecStalk x p
  have hι : Function.Injective ι := (Y.fromSpecStalk x).isEmbedding.injective
  rw [finsum_eq_sum_of_support_subset (s := P.image ι), Finset.sum_image fun _ _ _ _ h => hι h, Nat.cast_sum]
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [resCyc_eq hq hB t hj hx p ((hP p).1 hp).1 (hb p hp) rfl, mult_eq hA s hs hi p ((hP p).1 hp).1,
      Int.cast_natCast, Nat.cast_mul]
  · intro z hz
    obtain ⟨-, h1, h2, h3⟩ := of_term_ne_zero hq hA hB s t hs hz
    obtain ⟨p, rfl⟩ := (Scheme.range_fromSpecStalk (x := x)).ge h3
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨p, (hP p).2 ⟨(coheight_fromSpecStalk Y x p).symm.trans h1,
      not_not.1 (mt (mem_nonzeroLocus_iff_notMem s hi p).2 h2)⟩, rfl⟩)

end GlobalTheory.MixHt.CycLoc

namespace GlobalTheory.MixHt


open CycLoc in
theorem finsum_mult_resCyc_indicator_symm : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ (A B : LB Y) (hA : A.IsLB) (hB : B.IsLB) (s : A.Sec) (t : B.Sec) (hs : genericPoint Y ∈ nonzeroLocus s) (ht : genericPoint Y ∈ nonzeroLocus t), (∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → ∀ x : Y, ∑ᶠ z, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t (Set.indicator {x} 1) z = ∑ᶠ z, ((divOfSec hB t ht).mult z : ℝ) * resCyc hA s (Set.indicator {x} 1) z := by
  intro k _ Y _ _ q hq A B hA hB s t hs ht hst x
  by_cases hx : Order.coheight x = 2
  swap
  · rw [finsum_eq_zero_of_forall_eq_zero fun z => not_not.1 fun h => hx (of_term_ne_zero hq hA hB s t hs h).1,
      finsum_eq_zero_of_forall_eq_zero fun z => not_not.1 fun h => hx (of_term_ne_zero hq hB hA t s ht h).1]
  obtain ⟨i, hi⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hA x
  obtain ⟨j, hj⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hB x
  have ha := germ_ne_zero hs hi
  have hb := germ_ne_zero ht hj
  have hP := fun p => (finite_height_one _ _ ha).mem_toFinset (a := p)
  have hQ := fun p => (finite_height_one _ _ hb).mem_toFinset (a := p)
  have key (p : PrimeSpectrum (Y.presheaf.stalk x)) (h1 : p.asIdeal.height = 1)
      (h2 : Y.presheaf.germ _ x hi (s.f i) ∈ p.asIdeal) (h3 : Y.presheaf.germ _ x hj (t.f j) ∈ p.asIdeal) : False :=
    (hst _ ((coheight_fromSpecStalk Y x p).trans h1)).elim
      (fun h => (mem_nonzeroLocus_iff_notMem s hi p).1 h h2) fun h => (mem_nonzeroLocus_iff_notMem t hj p).1 h h3
  rw [finsum_eq hq hA hB s t hs hi hj hx _ hP fun p hp => key p ((hP p).1 hp).1 ((hP p).1 hp).2,
    finsum_eq hq hB hA t s ht hj hi hx _ hQ fun p hp h => key p ((hQ p).1 hp).1 h ((hQ p).1 hp).2]
  refine congrArg _ (_root_.GlobalTheory.IntersectionSymm.intersection_symm _ ?_ _ _ ha hb _ _ hP hQ (Finset.disjoint_left.2 fun p hp hp' =>
    key p ((hP p).1 hp).1 ((hP p).1 hp).2 ((hQ p).1 hp').2))
  rw [ringKrullDim_stalk_eq_coheight, hx]
  rfl

end GlobalTheory.MixHt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellCoordinatesContDiffAtEtaleChart
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2

open GlobalTheory.Points GlobalTheory.ChartGlue

theorem contDiffAt_chart_of_eqOn_ev {F : Type} [Field F] {Y : Var F} {σ : F →+* ℂ} {D : ℕ} (c' : AlgChart Y.str σ D)
    {g : CxPts Y.str σ → ℂ} {S : Set (CxPts Y.str σ)} (hS : IsOpen S) {W : Y.X.Opens} (a : Γ(Y.X, W))
    (hg : ∀ z ∈ S, g z = ev Y.str σ W a z) {y : CxPts Y.str σ} (hy : y ∈ c'.e.source) (hyS : y ∈ S)
    (hyW : y ∈ ptsIn Y.str σ W) : ContDiffAt ℂ 2 (g ∘ c'.e.symm) (c'.e y) := by
  have hO := isOpen_over c'.e (hS.inter (isOpen_ptsIn (p := Y.str) (σ := σ) W))
  have hm := mem_over c'.e (S := S ∩ ptsIn Y.str σ W) hy ⟨hyS, hyW⟩
  have hd : DifferentiableOn ℂ (ev Y.str σ W a ∘ c'.e.symm) (c'.e.target ∩ c'.e.symm ⁻¹' (S ∩ ptsIn Y.str σ W)) :=
    (c'.holo W a).mono fun v hv => ⟨hv.1, hv.2.2⟩
  have h1 : ContDiffAt ℂ 2 (ev Y.str σ W a ∘ c'.e.symm) (c'.e y) := ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ _ hO hd).contDiffAt (hO.mem_nhds hm)).of_le
    (by norm_cast)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hO.mem_nhds hm] with v hv
  exact hg _ hv.2.1

theorem cellMap_contDiffAt : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), ∀ (n : ℕ) (ε : Fin n ≃ Fin X.dim ⊕ Cell m) (x : (atlas Y σ).Pt), x.pt ∈ cellSet E E' φ f hf c A u → ContDiffAt ℂ 2 (cellMap ε f hf c u ∘ x.ch.symm) x.crd := by
  intro F _ σ X Y ι _ m E E' φ f hf hR c A u n ε x hx
  obtain ⟨hcell, hsrc⟩ := hx
  have hreg := (isOpen_inCell_and_regAt F X Y ι m E E' φ f hR A u).2 _ hcell
  set c' : AlgChart Y.str σ Y.dim := x.1.1
  have hy : x.pt ∈ c'.e.source := x.2
  change ContDiffAt ℂ 2 (cellMap ε f hf c u ∘ c'.e.symm) (c'.e x.pt)
  refine contDiffAt_euclidean.2 fun a => ?_
  change ContDiffAt ℂ 2 ((fun z => cellMap ε f hf c u z a) ∘ c'.e.symm) (c'.e x.pt)
  rcases hε : ε a with b | j
  · have hS : IsOpen (ptMap σ f hf ⁻¹' c.e.source) :=
      c.e.open_source.preimage (PtsOver.continuous_map f hf _)
    refine contDiffAt_chart_of_eqOn_ev c' hS (f.app c.U (c.x b)) (fun z hz => ?_) hy hsrc ?_
    · simp only [cellMap, pt, hε, Sum.elim_inl]
      rw [c.apply_eq _ hz b, ev_app f hf]
      rfl
    · rw [mem_ptsIn]
      exact mem_ptsIn.1 (c.source_subset hsrc)
  · obtain ⟨U, hU, w, hw⟩ := (hreg j).exists_fnOf
    refine contDiffAt_chart_of_eqOn_ev c' (isOpen_ptsIn U) w (fun z hz => ?_) hy (mem_ptsIn.2 hU) (mem_ptsIn.2 hU)
    simp only [cellMap, pt, hε, Sum.elim_inr]
    rw [← hw, ratVal_fnOf hz]

end GlobalTheory.FlagCell2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlaggedBundleMetricGradedWeightFrameIndependent
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc

theorem grWeight_frame_indep : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m m)
    (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ B ∈ E.S (genericPoint X.X), ∀ (y : CxPts X.str σ),
    ∀ A ∈ E.S (under y), ∀ A' ∈ E.S (under y), ∀ (x : Root m) (f : X.Fn), UnitAt (under y) ((B * A'⁻¹) x.1 x.2 x.2 / f) →
      -Real.log (‖ratVal ((B * A⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A y x.1) x.2) =
        -Real.log (‖ratVal ((B * A'⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A' y x.1) x.2) := by
  first
  | exact @_root_.GlobalTheory.LeadingMinorPositivity.green_frame_indep
  | exact _root_.GlobalTheory.LeadingMinorPositivity.green_frame_indep
  | (apply _root_.GlobalTheory.LeadingMinorPositivity.green_frame_indep <;> assumption)
  | (intros; apply _root_.GlobalTheory.LeadingMinorPositivity.green_frame_indep <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LeadingMinorPositivity.green_frame_indep <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LeadingMinorPositivity.green_frame_indep ..)

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFiniteTwistedKernelOverAffineParameter
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistFlat
open GlobalTheory.StabFlatLocal GlobalTheory.StabFlat GlobalTheory.UU

theorem flat_of_isFinite_twist : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V]
    (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ L : LB B.left, L.IsLB →
    (∃ t : LB.Gen (Theta B L), t.IsGen) → ∀ O : LB B.left, O.IsLB → (∃ u : LB.Gen (abelian₂ B O), u.IsGen) →
    ∀ (H : Over (Sp V)) (j : H ⟶ B), IsClosedImmersion j.left →
    (∀ (T : Over (Sp V)) (x : T ⟶ B), (∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι)) ↔
        ∃ y : T ⟶ H, y ≫ j = x) → IsFinite H.hom → Flat H.hom := by
  intro hG V _ _ _ B _ _ hB hp L hL hΘ O hO hu H j hj hH hf
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim V B hB
  rw [← Over.w j]
  refine _root_.GlobalTheory.StabFlat.flat_of_isFinite_of_ideals V B.left H.left B.hom j.left hj (by rw [Over.w j]; exact hf) fun h σ hσ hn => ?_
  have cl : ∀ (z : H.left) (p : Spec (B.left.presheaf.stalk (j.left h))),
      (IsLocalRing.maximalIdeal V).map σ ≤ p.asIdeal →
      j.left z = B.left.fromSpecStalk (j.left h) p → IsClosed ({j.left z} : Set B.left) := by
    intro z p hp e
    have hz : H.hom z = IsLocalRing.closedPoint V := by
      rw [← Over.w j, Scheme.Hom.comp_apply, e, ← Scheme.Hom.comp_apply, hσ]
      refine PrimeSpectrum.ext (Eq.symm ((IsLocalRing.maximalIdeal.isMaximal V).eq_of_le
        (PrimeSpectrum.isPrime _).ne_top ?_))
      exact Ideal.map_le_iff_le_comap.1 hp
    have := j.left.isClosedEmbedding.isClosedMap _ (isClosed_of_isFinite H.hom z hz)
    rwa [Set.image_singleton] at this
  have hm : (IsLocalRing.maximalIdeal V).map σ ≤ IsLocalRing.maximalIdeal _ :=
    Ideal.map_le_iff_le_comap.2 fun v hv => map_nonunit σ v hv
  obtain ⟨h₀, h₁, h₂, h₃⟩ := _root_.GlobalTheory.StabFlat.stalk_of_smooth_local V B.left B.hom g hg (j.left h)
    (cl h (IsLocalRing.closedPoint _) hm Scheme.fromSpecStalk_closedPoint.symm) σ hσ hn
  refine @exists_ideal hG V _ _ _ B _ _ hB hp g hg L O hL hO hΘ hu H j hH
    (B.left.presheaf.stalk (j.left h)) _ h₀ _
    (B.left.fromSpecStalk (j.left h)) σ hn h₁ h₂ h₃ (H.left.residueField h) _
    (j.left.stalkMap h ≫ H.left.residue h).hom
    (RingHom.isLocalHom_comp (IsLocalRing.residue (H.left.presheaf.stalk h)) (j.left.stalkMap h).hom) ⟨H.left.fromSpecResidueField h, ?_⟩ ?_
  · rw [Scheme.fromSpecResidueField, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Spec.map_comp_assoc]
    rfl
  · rintro K _ φ hφ ⟨y, hy⟩
    let p := Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint K)
    have hk : p.asIdeal = RingHom.ker φ := by
      show Ideal.comap φ (IsLocalRing.maximalIdeal K) = _
      rw [IsLocalRing.maximalIdeal_eq_bot, RingHom.ker_eq_comap_bot]
    have e : j.left (y (IsLocalRing.closedPoint K)) = B.left.fromSpecStalk (j.left h) p :=
      congrArg (fun q => q (IsLocalRing.closedPoint K)) hy
    have hc := cl _ p (hφ.trans hk.ge) e
    have hs : B.left.fromSpecStalk (j.left h) p ⤳ j.left h := by
      have : B.left.fromSpecStalk (j.left h) p ∈ Set.range (B.left.fromSpecStalk (j.left h)) := ⟨p, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have e' : j.left h = B.left.fromSpecStalk (j.left h) p := (hs.mem_closed hc e.symm).trans e
    have hp' : p = IsLocalRing.closedPoint _ := (B.left.fromSpecStalk (j.left h)).isEmbedding.injective
      (e'.symm.trans Scheme.fromSpecStalk_closedPoint.symm)
    rw [← hk, hp']
    rfl

end GlobalTheory.TwistFlat

namespace GlobalTheory.TwistFlat

theorem flat_local : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left,
    L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) (N : LB (A ⊗ T).left), Fam A N →
    ∀ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left →
    (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t) →
    ∀ (V : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] (φ : Sp V ⟶ T.left),
    IsFinite (pullback.snd (h ≫ snd A T).left φ) → Flat (pullback.snd (h ≫ snd A T).left φ) := by
  intro R _ A _ hA L hL ha T N hN H h hh hH V _ _ _ φ hfin
  have hB : IsAbelianScheme (bc A φ) := GlobalTheory.isAbelianScheme_pullback_obj _ A hA
  have : IsCommMonObj (bc A φ) := hB.comm
  have hP : IsProjBy (bc A φ).hom :=
    (GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ A L hA hL ha V (φ ≫ T.hom)
      _ (pullback.fst A.hom (φ ≫ T.hom)) (pullback.snd A.hom (φ ≫ T.hom)) (IsPullback.of_hasPullback _ _)).1
  have hL' : (L.pull (pullback.fst A.hom (φ ≫ T.hom))).IsLB := LB.isLB_pull hL _
  have hO : (twist A φ N).IsLB := pull_isLB hN.isLB _
  refine flat_of_isFinite_twist _root_.GlobalTheory.abelianSchemeLaws_all.1.globalFns V (bc A φ) hB hP _ hL'
    (GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy _root_.GlobalTheory.abelianSchemeLaws_all.1 _ _ hB hP _ hL') (twist A φ N) hO
    (GlobalTheory.T.lineBundleFamilyAtPoint_lambda_trivial A φ N hN) (ker A φ h) (kerι A φ h) (GlobalTheory.T.isClosedImmersion_fibreOverPointToBaseChange A φ h hh) (fun Y x => ?_) hfin
  rw [_root_.GlobalTheory.TwistFlat.factor_ker_iff A φ h Y x, ← hH, _root_.GlobalTheory.TwistFlat.same_lam_iff_locally_triv A T hA L hL N hN]
  exact forall_congr' fun p => exists_congr fun U => and_congr_right' (GlobalTheory.T.translationDifference_trivial_baseChange_iff_over_A A φ L hL N hN.isLB Y x U)

end GlobalTheory.TwistFlat

namespace GlobalTheory.TwistFlat

theorem isNoetherianRing_top (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) [IsAffine X]
    (f : X ⟶ Sp R) (hf : LocallyOfFiniteType f) : IsNoetherianRing Γ(X, ⊤) := by
  have h1 : (f.appTop).hom.FiniteType := (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).1 hf
  have : IsNoetherianRing Γ(Sp R, ⊤) :=
    isNoetherianRing_of_ringEquiv R (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  letI := (f.appTop).hom.toAlgebra
  have : Algebra.FiniteType Γ(Sp R, ⊤) Γ(X, ⊤) := h1
  exact Algebra.FiniteType.isNoetherianRing Γ(Sp R, ⊤) Γ(X, ⊤)

theorem flat_twisted_kernel : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ N : LB (A ⊗ T).left, Fam A N → ∀ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t) → IsFinite (h ≫ snd A T).left → Flat (h ≫ snd A T).left := by
  intro R _ _ A _ hA L hL ha T _ hT N hN H h hh hH hfin
  have : IsNoetherianRing Γ(T.left, ⊤) := isNoetherianRing_top R T.left T.hom hT
  let e := T.left.isoSpec
  let f := (h ≫ snd A T).left
  haveI : IsFinite f := hfin
  let H' : Over (Sp Γ(T.left, ⊤)) := Over.mk (f ≫ e.hom)
  have hfin' : IsFinite H'.hom := by
    show IsFinite (f ≫ e.hom)
    infer_instance
  have hflat : Flat (f ≫ e.hom) := by
    refine GlobalTheory.flat_of_isFinite_of_flat_localization_maximal Γ(T.left, ⊤) H' hfin' fun m _ => ?_
    let φ : Sp (Localization.AtPrime m) ⟶ T.left := spMap (algebraMap Γ(T.left, ⊤) (Localization.AtPrime m)) ≫ e.inv
    have hf : IsFinite (pullback.snd f φ) := MorphismProperty.of_isPullback (P := @IsFinite) (IsPullback.of_hasPullback f φ) hfin
    haveI := flat_local R A hA L hL ha T N hN H h hh hH (Localization.AtPrime m) φ hf
    have sq : IsPullback (pullback.fst f φ) (pullback.snd f φ) (f ≫ e.hom)
        (spMap (algebraMap Γ(T.left, ⊤) (Localization.AtPrime m))) :=
      (IsPullback.of_hasPullback f φ).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e (by simp) (by simp)
        (by simp) (by simp [φ])
    show Flat (pullback.snd (f ≫ e.hom) _)
    rw [← sq.isoPullback_inv_snd]
    infer_instance
  have hfe : f = (f ≫ e.hom) ≫ e.inv := by simp
  show Flat f
  rw [hfe]
  infer_instance

end GlobalTheory.TwistFlat
end
end

