module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextChangeSecondFactor
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValuationIntegersPadicComplete
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0126
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GeneratesOfNonzeroOnSpecialFibre
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0033
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0027
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEqSmulOne
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0158

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharactersBoundedMinorEigenspace
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.CharMinor

section SlopeTestRemainingChoices

open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs GlobalTheory.CharDepth IsLocalRing

theorem exists_minor_le {C : Type} [Field C] (V : VF C) (vm : Valuation C NNReal) (hT : ValuationFitting.ValTie V vm)
    (h0 : 0 < (vm (V.l : C) : ℝ)) (h1 : (vm (V.l : C) : ℝ) < 1) (hle : ∀ x : C, vm x ≤ 1 ↔ V.Ge 0 x)
    {m N : ℕ} (α : Matrix (Fin m) (Fin N) vm.integer) (xs : NNReal)
    (hx : ReciprocityTheory.PGsh.Up.HasLen vm vm.integer ((Fin m → vm.integer) ⧸ LinearMap.range α.mulVecLin) xs)
    (B : ℝ) (hB : (vm (V.l : C) : ℝ) ^ B ≤ xs) {n : ℕ} (w : Fin n → Fin m → C) (hw : IsSat V w) :
    ∃ g : Fin n → Fin N, V.v (Matrix.of fun ρ q : Fin n => ∑ x, (α x (g ρ) : C) * w q x).det ≤ (B : WithTop ℝ) := by
  have hv := Valuation.integer.integers vm
  obtain ⟨hw1, w', hw2, hww⟩ := hw
  let S : Matrix (Fin n) (Fin m) vm.integer := Matrix.of fun q x => ⟨w q x, (hle _).2 (hw1 q x)⟩
  let W : Matrix (Fin m) (Fin n) vm.integer := Matrix.of fun x q => ⟨w' x q, (hle _).2 (hw2 x q)⟩
  have hSW : S * W = 1 := by
    ext q q'
    have := hww q q'
    simp only [Matrix.mul_apply, Matrix.one_apply, S, W, Matrix.of_apply]
    push_cast
    rw [this]
    split_ifs <;> simp
  have hpos : 0 < (xs : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos h0 _) hB
  have e1 := ValuationFitting.lenCoker_eq_logb hT hv h0 h1 α hx hpos
  rw [← ValuationFitting.lenCoker_vA] at e1
  have e2 := S4.lenCoker_mul_le (ValuationFitting.vA V vm.integer) (ValuationFitting.vA_nonneg hT hv h0 h1) S W hSW α
  have e3 : Real.logb (vm (V.l : C) : ℝ) xs ≤ B := by
    rwa [← Real.rpow_logb h0 (ne_of_lt h1) hpos, Real.rpow_le_rpow_left_iff_of_base_lt_one h0 h1] at hB
  have e4 : S4.lenCoker (ValuationFitting.vA V vm.integer) (S * α) ≤ (B : WithTop ℝ) :=
    e2.trans (e1.le.trans (WithTop.coe_le_coe.2 e3))
  unfold S4.lenCoker at e4
  obtain ⟨g, -, hg⟩ := (Finset.inf_le_iff (WithTop.coe_lt_top B)).1 e4
  refine ⟨g, le_of_eq_of_le ?_ hg⟩
  rw [ValuationFitting.vA_apply, RingHom.map_det, ← Matrix.det_transpose]
  congr 2
  ext q ρ
  simp [Matrix.mul_apply, S, mul_comm]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _


open ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA ReciprocityTheory.ChartRestriction.G.TB.LogPf in
theorem isCh_map {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) {d : ℕ} (F : Fin d → PS R 2 d)
    (hF : ∀ i, MvPowerSeries.constantCoeff (F i) = 0) (u : PS R 1 d) (hu : IsCh F u) :
    IsCh (fun i => MvPowerSeries.map φ (F i)) (MvPowerSeries.map φ u) := by
  refine ⟨by rw [MvPowerSeries.constantCoeff_map, hu.1, map_one], ?_⟩
  have h := congrArg (MvPowerSeries.map φ) hu.2
  rw [map_mul, map_ev' φ (CZ.cons (cc_addOf' hF (cc_pt' 0) (cc_pt' 1)) CZ.nil),
    map_ev' φ (CZ.cons (cc_pt' 0) CZ.nil), map_ev' φ (CZ.cons (cc_pt' 1) CZ.nil)] at h
  simp only [mV_cons, mV_nil, mapPoint_addOf φ F (cc_pt' 0) (cc_pt' 1), mapPoint_pt] at h
  exact h

theorem span_res_eq {O : Type} [CommRing O] {d s N : ℕ} (W : Fin s → Fin d → O) (u : Fin N → PS O 1 d) :
    Submodule.span O (Set.range fun k => res W (dl (u k))) =
      LinearMap.range (Matrix.of fun x k => res W (dl (u k)) x).mulVecLin := by
  rw [Matrix.range_mulVecLin]
  rfl

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

theorem family_cast_iff {A : Type} (P : ∀ s : ℕ, (Fin s → A) → Prop) {ι : Type} {r : ι → ℕ} (g : ∀ i, Fin (r i) → A)
    {i j : ι} (h : i = j) : P _ (g i) ↔ P _ (g j) := by
  subst h; rfl

theorem colength_bound (p : ℕ) [Fact p.Prime] (hU : UpFSt p) (hp2 : p ≠ 2) (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) :
    letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y)
    (X : ValExt T p), y.IsAlg → ¬ (p : ℤ) ∣ NumberField.discr E →
    ∀ (d : ℕ) [NeZero d] (tau : ZMod d → (E →+* ℂ)), Function.Injective tau →
    (∀ s x, X.v (X.ιF (io (embK c (tau (s + 1)) x)) - X.ιF (io (embK c (tau s) x)) ^ p) < 1) →
    ∀ s : ZMod d, ∃ xs : NNReal, HasAF X.v (fun i => MvPowerSeries.map X.ι (Ch.FT i))
      (fun (i : Fin (Dw.mult (tau s))) j => X.ι (Ch.uvecT ⟨tau s, i⟩ j)) xs ∧
      (X.v (p : X.C) : ℝ) ^ (∑' i : ℕ, ((p : ℝ) ^ (-((i : ℝ) + 1))) *
        (Dw.mult (ComplexEmbedding.conjugate (tau (s + ((i + 1 : ℕ) : ZMod d)))) : ℝ)) ≤ xs := by
  letI := H.starRing
  intro T io y Ch X hy hdisc d _ tau htau hfrob s
  obtain ⟨U⟩ := GlobalTheory.CharDepth.nonempty_unifChart E H Dw l Xo c T io y Ch hy p X
  obtain ⟨τT, -, hty, hinj, -, hconj⟩ := exists_types_valuationRing E H l c T io p X
  set τO : (E →+* ℂ) → (𝓞 E →+* X.O) := fun τ => X.ι.comp (τT τ) with hτO
  have heig := fun τ => (isEigBasis_valExt E H Dw l Xo c T io y Ch p X τO hty τ).1
  have hcard := (GlobalTheory.EmbCount.card_emb E p X.C X.v X.O X.ints 0 (by simp)).2
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  haveI : Finite (𝓞 E →+* X.O) := Nat.finite_of_card_ne_zero (by omega)
  have hbij : Function.Bijective τO := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [hcard, Nat.card_eq_fintype_card, NumberField.Embeddings.card E ℂ]
  let e := Equiv.ofBijective τO hbij
  have he : ∀ τ, e.symm (τO τ) = τ := fun τ => e.symm_apply_apply τ
  have hfr : ∀ s x, τO (tau (s + 1)) x - τO (tau s) x ^ p ∈ maximalIdeal X.O := by
    intro s x
    rw [mem_maximalIdeal, mem_nonunits_iff, X.ints.isUnit_iff_valuation_eq_one, map_sub, map_pow, hty, hty]
    exact (hfrob s x).ne
  obtain ⟨w, hwn, t, ht, hb⟩ := GlobalTheory.OrbitPlace.exists_placeU_of_frobenius_orbit E p X.C X.v X.O X.ints X.nonunit.out hdisc d (fun s => τO (tau s))
    (hinj.comp htau) hfr
  subst hwn
  have hact : actMap U.ι' U.act = fun a i => MvPowerSeries.map X.ι (Ch.actT a i) := funext U.act_eq
  have hnu : ¬ IsUnit ((p : U.T'.V)) := fun h => X.nonunit.out (by have h' := h.map U.ι'; rwa [map_natCast] at h')
  have hd' : ¬ ((p : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ (𝓞 E))) := by
    rwa [NumberField.discr_eq_discr E (Module.Free.chooseBasis ℤ (𝓞 E))]
  have hadd : ∀ (j : Fin w.n) (k : ℕ), (((j + Fin.ofNat w.n k : Fin w.n).val : ℕ) : ZMod w.n) =
      ((j.val : ℕ) : ZMod w.n) + (k : ZMod w.n) := by
    intro j k
    rw [Fin.val_add, ZMod.natCast_mod, Nat.cast_add, Fin.val_ofNat, ZMod.natCast_mod]
  have hone : ∀ j : Fin w.n, (((j + 1 : Fin w.n).val : ℕ) : ZMod w.n) = ((j.val : ℕ) : ZMod w.n) + 1 := by
    intro j
    have := hadd j 1
    rwa [Nat.cast_one] at this
  let j0 : Fin w.n := ⟨s.val, ZMod.val_lt s⟩
  have hj0 : ((j0.val : ℕ) : ZMod w.n) = s := ZMod.natCast_zmod_val s
  obtain ⟨xs, hxs, hle⟩ := hU U.T'.V hnu U.t.G U.P.D U.P.A U.P.U.toUnifPre _ U.F U.x U.chart hp2 (𝓞 E)
    U.t.act.toRingAct U.P.oD U.P.oA U.P.lin hd' U.act U.acts X.C X.v X.O X.ints U.ι' U.ι'_local w t hb
    (fun j a => by rw [ht, ht, hone]; exact hfr _ a)
    (fun σ => Dw.mult (e.symm σ)) (fun σ i k => X.ι (Ch.uvecT ⟨e.symm σ, i⟩ k))
    (fun σ => by
      rw [hact]
      have := heig (e.symm σ)
      rwa [show τO (e.symm σ) = σ from e.apply_symm_apply σ] at this) j0
  refine ⟨xs, ?_, ?_⟩
  · rw [← U.law_eq]
    refine (family_cast_iff (fun _ g => HasAF X.v (U.F.mapF U.ι') g xs)
      (fun (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) k => X.ι (Ch.uvecT ⟨τ, i⟩ k)) ?_).1 hxs
    rw [ht, hj0, he]
  · have h2 := NNReal.coe_le_coe.2 hle
    rw [NNReal.coe_rpow, map_natCast] at h2
    refine le_of_eq_of_le ?_ h2
    congr 1
    refine tsum_congr fun i => ?_
    rw [ht, hadd, hj0]
    congr 3
    rw [Equiv.eq_symm_apply]
    ext a
    show X.ι (τT _ a) = X.ι (τT _ _)
    rw [hconj]
    rfl

end SlopeTestRemainingChoices

theorem exists_chars_minor_le : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → y.IsAlg → ¬ (V.l : ℤ) ∣ NumberField.discr E → ∀ (d : ℕ) [NeZero d] (tau : ZMod d → (E →+* ℂ)), Function.Injective tau → FrobOrd V io ι tau → ∀ (s : ZMod d) (n : ℕ) (w : Fin n → Fin (Dw.mult (tau s)) → C), IsSat V w → ∃ χ : Fin n → PS C 1 (chD C3.ch), (∀ ρ, IntS V (χ ρ) ∧ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.IsCh Y.B.G.F (χ ρ)) ∧ V.v (Matrix.of fun ρ q : Fin n => ∑ x, (∑ i, ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.dl (χ ρ) i * ι (chartUnitVectors C3 ⟨tau s, x⟩ i)) * w q x).det ≤ (((∑' i : ℕ, ((V.l : ℝ) ^ (-((i : ℝ) + 1))) * (Dw.mult (ComplexEmbedding.conjugate (tau (s + ((i + 1 : ℕ) : ZMod d)))) : ℝ)) : ℝ) : WithTop ℝ) := by
  intro hU E _ _ _ H Dw lv Xo c inst hstar
  obtain rfl : inst = H.starRing := GlobalTheory.PowGerm.starSt E H inst hstar
  letI := H.starRing
  intro T io y C3 C _ _ V ι hι k Y hY hy hdisc d _ tau htau hfrob s n w hw
  haveI := Y.algClosed
  haveI : Fact V.l.Prime := ⟨V.l_prime⟩
  obtain ⟨vm, hT, h0, h1, hle, hlt, hcpl, ⟨hzp⟩⟩ := GlobalTheory.ValExp.exists_mulVal C V Y.cpl
  have hv := Valuation.integer.integers vm
  let ιO : T.V →+* vm.integer := (ι.comp (algebraMap T.V T.Fr)).codRestrict vm.integer
    fun t => (hle _).2 (embIntSt_holds T C V ι hι t)
  have hl0 : ((V.l : ℕ) : T.Fr) ≠ 0 := by exact_mod_cast V.l_prime.ne_zero
  have hvl : (vV T.V ((V.l : ℕ) : T.Fr) : ℝ) ≠ 0 := by
    intro h
    have := hι _ hl0
    rw [map_natCast, V.v_l, h, div_zero] at this
    exact one_ne_zero (by exact_mod_cast this : (1 : ℝ) = 0)
  have hval : ∀ x : T.Fr, x ≠ 0 → (vm (ι x) : ℝ) =
      (vm (V.l : C) : ℝ) ^ ((vV T.V x : ℝ) / (vV T.V (V.l : T.Fr) : ℝ)) := by
    intro x hx
    obtain ⟨t, ht1, ht2⟩ := hT (ι x) ((map_ne_zero ι).2 hx)
    rw [hι x hx] at ht1
    rw [ht2, WithTop.coe_injective ht1]
  have hloc : IsLocalHom ιO := ⟨fun a ha => by
    have h2 : vm (ι (algebraMap T.V T.Fr a)) = 1 := hv.isUnit_iff_valuation_eq_one.1 ha
    have ha0 : algebraMap T.V T.Fr a ≠ 0 := by
      intro h; rw [h, map_zero, map_zero] at h2; exact zero_ne_one h2
    have h3 := hval _ ha0
    rw [h2, NNReal.coe_one, eq_comm, ← Real.rpow_zero (vm (V.l : C) : ℝ),
      Real.rpow_right_inj h0 h1.ne, div_eq_zero_iff, or_iff_left hvl, Int.cast_eq_zero] at h3
    have h4 : valV T.V (algebraMap T.V T.Fr a) = 1 := by
      have h5 := WithZero.exp_log (valV_ne_zero (V := T.V) ha0)
      unfold vV at h3
      rw [neg_eq_zero] at h3
      rw [← h5, h3, WithZero.exp_zero]
    by_contra hna
    have h6 : valV T.V (algebraMap T.V T.Fr a) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem _ a).2 hna
    exact h6.ne h4⟩
  have hnu : Fact (¬ IsUnit ((V.l : ℕ) : vm.integer)) := ⟨by
    rw [hv.isUnit_iff_valuation_eq_one, map_natCast]
    intro h; rw [h] at h1; simp at h1⟩
  let X : GlobalTheory.CharDepth.ValExt T V.l :=
    { C := C, v := vm, O := vm.integer, ints := hv, nonunit := hnu, cpl := hcpl, zp := hzp, ι := ιO,
      ι_local := hloc, ιF := ι, comp := fun _ => rfl, val := hval }
  obtain ⟨xs, ⟨N, u, hu, hlen⟩, hB⟩ := colength_bound V.l (hU V.l) Y.l_odd E H Dw lv Xo c T io y C3 X hy hdisc d
    tau htau (fun s x => (hlt _).2 (hfrob s x)) s
  rw [span_res_eq] at hlen
  obtain ⟨g, hg⟩ := exists_minor_le V vm hT h0 h1 hle _ xs hlen _ hB w hw
  have hF : Y.B.G.F = fun i => MvPowerSeries.map (algebraMap vm.integer C) (MvPowerSeries.map ιO (C3.FT i)) := by
    funext i
    rw [hY.F i, show (a3B C3).G.F i = _ from C3.gen.1.1 i]
    rfl
  refine ⟨fun ρ => MvPowerSeries.map (algebraMap vm.integer C) (u (g ρ)), fun ρ => ⟨fun μ => ?_, ?_⟩, ?_⟩
  · exact (hle _).1 (MvPowerSeries.coeff μ (u (g ρ))).2
  · rw [hF]
    refine isCh_map _ _ (fun i => ?_) _ (hu (g ρ))
    apply Subtype.ext
    have := Y.B.G.const i
    rw [hF] at this
    exact this
  · refine le_of_eq_of_le ?_ hg
    congr 2
    ext ρ q
    rw [Matrix.of_apply, Matrix.of_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    simp only [Matrix.of_apply, ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.res, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
    refine Eq.trans ?_ (map_sum (algebraMap vm.integer C) _ _).symm
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show chartUnitVectors C3 ⟨tau s, x⟩ i = _ from C3.gen.1.2.2.2.2.2.2 _ i, mul_comm]
    rfl

end GlobalTheory.CharMinor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsExtensionAllModelsUniformized
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.IntegralPull

theorem exists_ext_all_models_uniformised : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (y' : IntFr Xo c T' io') (e' : ℕ), y'.IsAlg ∧ 0 < e' ∧ (∀ I : IntData Xo c T' io' y'.1, ∃ P : PELUnif (maximalIdeal T'.V) I.G, P.TorsionIso) ∧ letI := io.toAlgebra; letI := io'.toAlgebra; ∃ φ : T.Fr →ₐ[c.F] T'.Fr, (∀ a : T.Fr, a ≠ 0 → vV T'.V (φ a) = (e' : ℤ) * vV T.V a) ∧ FrMap φ y.1 y'.1 := by
  intro E _ _ _ H Dw l Xo c T io y hy
  have hy' : T.FinRes := hy
  obtain ⟨y, hft, hint⟩ := y
  have hint0 := hint
  obtain ⟨G, t', m1, m2, -⟩ := hint
  have : Finite (ResidueField T.V) := hy'
  obtain ⟨W', _, _, _, _, _, hfin, hinj, hres, hS⟩ :=
    GlobalTheory.UnifAfterExt.exists_split_baseChange T.V G.G G.semi
  have : CharZero W' := charZero_of_injective_algebraMap hinj
  let T' : Formalism.L2.Pj.CDVR :=
    { V := W', cr := inferInstance, dom := inferInstance, dvr := inferInstance, cpl := inferInstance,
      ch0 := inferInstance }
  have hg : Function.Injective ((algebraMap T'.V T'.Fr).comp (algebraMap T.V W')) :=
    (IsFractionRing.injective T'.V T'.Fr).comp hinj
  let ψ : T.Fr →+* T'.Fr := IsFractionRing.lift hg
  have hψ : ∀ a, ψ (algebraMap T.V T.Fr a) = algebraMap T'.V T'.Fr (algebraMap T.V W' a) :=
    fun a => IsFractionRing.lift_algebraMap hg a
  letI := io.toAlgebra
  letI := (ψ.comp io).toAlgebra
  let φ : T.Fr →ₐ[c.F] T'.Fr := { ψ with commutes' := fun _ => rfl }
  obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1 E H Dw l Xo c T.Fr T'.Fr φ y
  have hzT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := by
    unfold FromTest at hft ⊢
    obtain ⟨p, φ0, y0, h0⟩ := hft
    exact ⟨p, φ.comp φ0, y0, ((GlobalTheory.framedPoint_baseChange_laws E H Dw l Xo c).2.1 _ _ _ φ0 φ y0 y z h0).1 hz⟩
  have hzI : Integral T' (ψ.comp io) z :=
    integral_baseChange T T' io (ψ.comp io) (algebraMap T.V W') hinj φ (fun a => hψ a) y z hz hint0
  have : Module.Finite T.V W' := hfin
  have : FaithfulSMul T.V W' := (faithfulSMul_iff_algebraMap_injective T.V W').mpr hinj
  have : IsLocalHom (algebraMap T.V W') := inferInstance
  obtain ⟨r, hr0, hr⟩ := exists_index (K' := T.Fr) (K'' := T'.Fr) (algebraMap T.V W') ψ hψ
  have hx : z.x = spMap ψ ≫ y.x := hz.1
  refine ⟨T', ψ.comp io, ⟨z, hzT, hzI⟩, r, hres, hr0, ?_, φ, fun a _ => hr a, hz⟩
  intro I'
  exact exists_unif_of_split T T' (algebraMap T.V W') ψ hψ m1 m2 hx I'.m1 I'.m2 hS

end GlobalTheory.IntegralPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLevelChangeActionOnCuspForms
section
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

theorem exists_isLevAct : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (P : Type) (ℓ : P → (LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l)), ∃ act, IsLevAct T h j w ℓ act := by
  intro D T h j hj w P ℓ
  have e : cutR T.C j w = T.cuspA j (wtA w) w.n := cutR_eq T.C hj w
  refine ⟨fun g F => (⟨actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) (ℓ g) F.1, ?_⟩ : cutR T.C j w), fun g F => rfl⟩
  exact e.ge (GlobalTheory.T.levelAction_mem_cuspForms D T h j hj w (ℓ g) F.1 (e.le F.2))

end GlobalTheory.FormTies
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsShortBasisUniformizationLattice
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.ShortBasisAt

theorem rootDiscriminantDegreeRatio_eq (D : D7) : rr0 D = D.host.rdE ^ 2 / (4 * D.R.f) := by
  unfold rr0 Formalism.BasicNotions.Host.rdE
  rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), GlobalTheory.PinNum.finrank_host]
  push_cast
  congr 1
  · congr 1
    ring
  · ring

theorem exists_shortBasis : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (T' : CDVR) (io : T.Q.c.F →+* T'.Fr) (e : ℕ) (ho : OverLa la T'.V io e) (z : IntFr (T.Q.Xo j) T.Q.c T' io) (hz : z.IsAlg) (η : T.G.PY j (WeightAlgebra.resCh la)) (hl : T.G.lies j la T' io z η), letI := T.Q.H.starRing; ∀ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c T' io z) (P : PELUnif (maximalIdeal T'.V) C.I.G) (ϖ : T'.V), Irreducible ϖ → ∀ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q → ∃ (r : ℕ) (Φ M0 : ℝ), ShortBasis Q r Φ M0 ∧ r ≤ 2 * D.R.f * D.R.m ∧ M0 ≤ 2 * Real.sqrt (2 * D.R.f * D.R.m) ∧ (D.R.m ≤ j → M0 = 0 ∧ Φ = 0) ∧ Φ ≤ e * (rr0 D * (2 * D.R.f * D.R.m : ℝ) ^ 3 * (recPJ h j hj).phiC la (PtV.mk la ho z hz η hl)) := by
  intro D T h j hj la T' io e ho z hz η hl C P ϖ hϖ Q hQ
  by_cases hm : j < D.R.m
  · obtain ⟨h0, r, b, hr, h1, h2⟩ :=
      GlobalTheory.PhiTie.exists_reduced_basis_le_phiCy D T h j hj hm la T' io e z ho hz η hl C P ϖ hϖ Q hQ
    have hφ : (recPJ h j hj).phiC la (PtV.mk la ho z hz η hl) =
        (ramOverZ la : ℝ) * (T.G.P.loc (T.G.dat j) (WeightAlgebra.resCh la)).phiCy η := by
      rw [← H1algLink.eWL_eq la]
      exact ConjugateMinimaInstance.phiC_rec_eq (recPJ h j hj) hm la _
    rw [hφ, rootDiscriminantDegreeRatio_eq]
    have hr' : (r : ℝ) ≤ 2 * D.R.f * D.R.m := by exact_mod_cast hr
    refine ⟨r, _, _, ⟨by positivity, b, h1, h2⟩, hr, by push_cast; exact le_rfl, fun h' => absurd hm (not_lt.2 h'), ?_⟩
    gcongr
  · letI := io.toAlgebra
    letI := T.Q.H.starRing
    obtain ⟨ρ, hρ, -, hq⟩ := GlobalTheory.ToricRank.rank_le_signature D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T'.V C.I.G P
      C.I.t' C.I.m2 z.1.x C.I.m1 inferInstance
    have hq' : ρ ≤ D.R.m - j := hq.trans_eq (h.toLawsCore.pins.2.2.2 j hj).2.1
    have h0 : Module.finrank ℤ P.D.toPre.X = 0 := by
      rw [hρ, show ρ = 0 by omega, mul_zero]
    have hφ : (recPJ h j hj).phiC la (PtV.mk la ho z hz η hl) = 0 := if_neg hm
    refine ⟨0, 0, 0, ⟨le_rfl, Module.finBasisOfFinrankEq ℤ _ h0, fun i => i.elim0, fun i => i.elim0⟩, Nat.zero_le _,
      by positivity, fun _ => ⟨rfl, rfl⟩, ?_⟩
    rw [hφ]; simp

end GlobalTheory.ShortBasisAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IInfThetaGeneratorsLeLocalDepthPrimeToLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

namespace GlobalTheory.ThetaLeast

theorem iInf_thGen_le_nuLocC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
 letI := H.starRing
 ∀ (nab : NabV Xo c), IsNab Xo c nab → ThValTot Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → y.IsAlg → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) → (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) → ∀ (α : 𝓞 E), α * star α = ((l.M : ℕ) : 𝓞 E) → l.Mb = Ideal.span {star α} → IsUnit ((l.M : ℕ) : T.V) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n Dg e : ℕ), 1 ≤ n → 0 < e → DF Dw a ≤ Dg → 4 * Dg + 4 ≤ l.M → (Dg : ℝ) * M0 < l.M → (⨅ f ∈ thGen Xo c nab a n, nval T.V e (evI y f)) ≤ nuLocC C e l.M a n + (((Dg : ℝ) ^ 2 * Φ / l.M / e : ℝ) : EReal) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro nab hnab hth T io y C hTr P hP hy ϖ hϖ Q hQ Φ M0 r b hΦ hb hb' α hα hMb hu a n Dg e hn he hD h4 hM0
  letI := io.toAlgebra
  obtain ⟨F, _, _, _, _, _, _, v, hv, hvx⟩ : ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (_ : CharZero F)
      (_ : Algebra T.Fr F) (_ : Algebra T.V F) (_ : IsScalarTower T.V T.Fr F) (v : AddValuation F (WithTop ℚ)),
      ValOver ϖ F v ∧ ∀ x : T.Fr, x ≠ 0 → v (algebraMap T.Fr F x) = (((vV T.V x : ℤ) : ℚ) : WithTop ℚ) := by
    obtain ⟨v, hv⟩ := GlobalTheory.ValClosure.exists_valuation_closure T.V ϖ hϖ
    exact ⟨AlgebraicClosure T.Fr, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, v, hv⟩
  obtain ⟨TI⟩ := GlobalTheory.T.nonempty_tateIsometry_integralFramedPoint_chart E H Dw l Xo c T io y C P F
  obtain ⟨D', A', G', _, _, pD, pA, pG, U', PU, _, oD', hx, hact, hθ⟩ :=
    (GlobalTheory.T.exists_productData_copies_trivialisation_valuation E H Dw l Xo c T io y C P ϖ hϖ).2 n
  obtain ⟨θ, θα, hθ1, hθ2, hθ3⟩ := hθ F v hv Q hQ α l.M (by have := l.three_le; omega) hα
  have hcop : ∃ u u' : 𝓞 E, u * α + u' * star α = 1 := by
    have h1 := l.coprime
    rw [hMb, Ideal.map_span, Set.image_singleton] at h1
    have h2 : (H.bar : 𝓞 E →+* 𝓞 E) (star α) = α := star_star α
    rw [h2, sup_comm, ← Ideal.span_insert, Ideal.eq_top_iff_one, Ideal.mem_span_pair] at h1
    exact h1
  unfold nuLocC
  refine le_iInf_add_coe fun Pp => le_iInf_add_coe fun hPp => le_iInf_add_coe fun f => le_iInf_add_coe fun hf => ?_
  set x0 := nabValN C.ch.B T.Fr C.ch.h H.w0 l.M f (fun ℓ : LtN Dw n => ℓ.2.2)
    (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) Pp with hx0def
  by_cases hx0 : x0 = 0
  · rw [hx0, nval_zero, EReal.top_add_coe]; exact le_top
  obtain ⟨s, cf, Qs, hQs, hsum⟩ := exists_combination_integers c.F T io _ _ n _ _ _ Pp hPp
  have hmap : (∑ i, algebraMap T.Fr F (algebraMap T.V T.Fr (cf i)) •
      MvPolynomial.map ((algebraMap T.Fr F).comp io) (Qs i)) = MvPolynomial.map (algebraMap T.Fr F) Pp := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_map]
  have hdeg : (MvPolynomial.map (algebraMap T.Fr F) Pp).totalDegree ≤ Dg :=
    (Finset.sup_mono (MvPolynomial.support_map_subset _ _)).trans ((totalDegree_le_DF T hPp).trans hD)
  have hval := nabValN_algebraMap T.Fr F _ _ C.ch.B C.ch.h (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.cc_h C.ch.gauge) H.w0 l.M n f
    (LtN Dw n) (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) Pp
  obtain ⟨i, p, w, ζ, x, t₀, t, σ', h, ρ, h1, h2, h3, h4', h5, h6, h7, h8, h9, hρ, hle⟩ :=
    _root_.GlobalTheory.PowGerm.pointStatements_on_copies.1 E H Dw l Xo c T io y C hTr P hP hy ϖ hϖ Q hQ F v hv TI Φ M0 r b hΦ hb hb' n D' A' G' pD pA pG U' PU
      oD' hx hact hn α l.M Dg hα hcop hu h4 hM0 θ θα hθ1 hθ2 hθ3 (Fin s)
      (fun i => MvPolynomial.map ((algebraMap T.Fr F).comp io) (Qs i))
      (fun i => algebraMap T.Fr F (algebraMap T.V T.Fr (cf i))) (fun i => val_algebraMap_nonneg T v hvx _)
      (by rw [hmap]; exact hdeg) f hf ((vV T.V x0 : ℤ) : ℚ)
      (by rw [hmap, Nat.one_mul, hval]; exact hvx x0 hx0)
  obtain ⟨g, hg, ε, hε, hgv⟩ := GlobalTheory.T.value_translate_pullback_eq_generator' E H Dw l Xo c nab hnab hth T io y C hTr P hP hy ϖ hϖ Q hQ F v hv n D' A' G'
    pD pA pG U' PU oD' hx hact α hα hMb θ θα hθ1 hθ2 hθ3 p w ζ x t₀ t σ' h h1 h2 h3 h4' h5 h6 h7 h8 h9 a (Qs i) (hQs i)
  rw [hgv] at hρ
  have hint : ∀ τ : E →+* ℂ, ∃ z : T.V, algebraMap T.V T.Fr z = io (embK c τ α) := fun τ => by
    obtain ⟨φ, hφ⟩ := exists_lift_integers E T.V T.Fr (io.comp (embF c τ))
    exact ⟨φ α, hφ α⟩
  choose z hz using hint
  have hε' : 0 ≤ v (ε * ∏ τ : E →+* ℂ, algebraMap T.Fr F (io (embK c τ α)) ^ (∑ i : Fin (Dw.mult τ), a (τ, i))) := by
    rw [AddValuation.map_mul]
    refine add_nonneg hε ?_
    have := val_algebraMap_nonneg T v hvx (∏ τ : E →+* ℂ, z τ ^ (∑ i : Fin (Dw.mult τ), a (τ, i)))
    simpa only [map_prod, map_pow, hz] using this
  exact (iInf₂_le g hg).trans (nval_le_of_val T v hvx hx0 hε' hρ hle e)

end GlobalTheory.ThetaLeast
end

