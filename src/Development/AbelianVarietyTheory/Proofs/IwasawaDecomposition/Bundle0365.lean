module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitPlaceEqOfPlaceEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0310
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdB
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Formalism.LocalToGlobal.Columns.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0361
public import Formalism.LocalToGlobal.Columns.ColumnsProofs.HeckeFieldSplit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0358
public import ReciprocityTheory.GaloisValuations.Global
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0353

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientLinearLiftDoubleCosetOperators
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeLiftN

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem unif_ne_zero {s : SplitPlace L} {ϖ : s.v.adicCompletion (maximalRealSubfield L)}
    (hϖ : IsUnif L s.v ϖ) : ϖ ≠ 0 := by
  rintro rfl
  have : Valued.v (0 : s.v.adicCompletion (maximalRealSubfield L)) = WithZero.exp (-1 : ℤ) := hϖ
  rw [map_zero] at this
  exact WithZero.exp_ne_zero this.symm

theorem tSet_subset_of_unif (n : ℕ) (s : SplitPlace L) (ϖ ϖ' : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ)
    (hϖ : IsUnif L s.v ϖ) (hϖ' : IsUnif L s.v ϖ') : tSet L n s ϖ k ⊆ tSet L n s ϖ' k := by
  rintro x ⟨hx, a, ha, b, hb, e⟩
  have h0 := unif_ne_zero hϖ'
  have h0' := unif_ne_zero hϖ
  set u := ϖ / ϖ' with hu
  have hu0 : u ≠ 0 := div_ne_zero h0' h0
  have hv : Valued.v u = 1 := by
    rw [hu, map_div₀]
    have e1 : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
    have e2 : Valued.v ϖ' = WithZero.exp (-1 : ℤ) := hϖ'
    rw [e1, e2, div_self WithZero.exp_ne_zero]
  have hvi : Valued.v u⁻¹ = 1 := by rw [map_inv₀, hv, inv_one]
  let c : Fin n → s.v.adicCompletion (maximalRealSubfield L) := fun i => if (i : ℕ) < k then u else 1
  let c' : Fin n → s.v.adicCompletion (maximalRealSubfield L) := fun i => if (i : ℕ) < k then u⁻¹ else 1
  have hcc : (fun i => c i * c' i) = fun _ => 1 := by
    funext i; simp only [c, c']; split_ifs <;> simp [hu0]
  have hcc' : (fun i => c' i * c i) = fun _ => 1 := by
    funext i; simp only [c, c']; split_ifs <;> simp [hu0]
  let dm : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) :=
    ⟨Matrix.diagonal c, Matrix.diagonal c', by rw [Matrix.diagonal_mul_diagonal, hcc, Matrix.diagonal_one],
      by rw [Matrix.diagonal_mul_diagonal, hcc', Matrix.diagonal_one]⟩
  have hI : ∀ z : s.v.adicCompletion (maximalRealSubfield L), Valued.v z ≤ 1 →
      z ∈ (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := fun z hz =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ s.v).2 hz
  have hdm : dm ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := by
    rw [GlobalTheory.HeckeStdFacts.mem_GLint_iff]
    refine ⟨fun i j => hI _ ?_, fun i j => hI _ ?_⟩
    · show Valued.v (Matrix.diagonal c i j) ≤ 1
      rw [Matrix.diagonal_apply]
      split_ifs
      · simp only [c]; split_ifs
        · rw [hv]
        · rw [map_one]
      · rw [map_zero]; exact zero_le'
    · show Valued.v (Matrix.diagonal c' i j) ≤ 1
      rw [Matrix.diagonal_apply]
      split_ifs
      · simp only [c']; split_ifs
        · rw [hvi]
        · rw [map_one]
      · rw [map_zero]; exact zero_le'
  have hdiag : Formalism.UG.diagJ n ϖ k = Formalism.UG.diagJ n ϖ' k * (dm : Matrix (Fin n) (Fin n) _) := by
    show _ = _ * Matrix.diagonal c
    rw [Formalism.UG.diagJ, Formalism.UG.diagJ, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [c]
    split_ifs
    · rw [hu]; field_simp
    · rw [one_mul]
  refine ⟨hx, a, ha, dm * b, mul_mem hdm hb, ?_⟩
  rw [e, Units.val_mul, hdiag]
  simp only [Matrix.mul_assoc]

theorem tSet_eq_of_unif (n : ℕ) (s : SplitPlace L) (ϖ ϖ' : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ)
    (hϖ : IsUnif L s.v ϖ) (hϖ' : IsUnif L s.v ϖ') : tSet L n s ϖ k = tSet L n s ϖ' k :=
  Set.Subset.antisymm (tSet_subset_of_unif n s ϖ ϖ' k hϖ hϖ') (tSet_subset_of_unif n s ϖ' ϖ k hϖ' hϖ)

theorem tN_eq_of_conj (D : D7) {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (J : Subgroup (GAf D.host.E n))
    (v : PlE D.host) (s s' : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E))
    (ϖ' : s'.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ) (hc : IsConjPl D.host v s.w)
    (hc' : IsConjPl D.host v s'.w) (hu : IsUnif D.host.E s.v ϖ) (hu' : IsUnif D.host.E s'.v ϖ') (f : GAf D.host.E n → W) :
    NG.tN J s ϖ k f = NG.tN J s' ϖ' k f := by
  have hw : s.w = s'.w := GlobalTheory.TwSys.ResidualCompare.isConjPl_unique hc hc'
  obtain rfl := GlobalTheory.SplitUniq.splitPlace_eq_of_w_eq _ s s' hw
  unfold NG.tN
  rw [tSet_eq_of_unif n s ϖ ϖ' k hu hu']

end GlobalTheory.HeckeLiftN

namespace GlobalTheory.HeckeLiftN

theorem heckeLift (D : D7) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) :
    HeckeStdPlain → GenHyp M C.Q → MtInput D M tup C.Q → HeckeLift0 (mt0 M) C.Q := by
  intro hP hG hI j w v k h1 h2 hg
  classical
  by_cases hex : ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
      IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ
  swap
  · exact ⟨0, fun s ϖ hc hu _ => absurd ⟨s, ϖ, hc, hu⟩ hex⟩
  obtain ⟨s0, ϖ0, hc0, hu0⟩ := hex
  obtain ⟨B, hB, hBs⟩ := hG w j h1 h2
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hj' : j' < D.R.m := by omega
  set Mw := M (D.what₂.muTw w) (j' + 1) h1 h2 with hMw
  have hrat : ∀ x, ∃ x', Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) x') =
      NG.tN Mw.J s0 ϖ0 k (Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) x)) :=
    fun x => hI.rat w ⟨j', hj'⟩ v k s0 ϖ0 hg hc0 hu0 x
  obtain ⟨-, Plin, -, -⟩ := hP D.host.E D.R.nV Mw.wt Mw.J Mw.χ B Mw.J_open hB s0 ϖ0 k (hBs v k s0 hg hc0) hu0
    hg.2.2.2.2.1 hg.2.2.2.2.2
  have hTS : ∀ y, Mw.real y ∈ NG.TypeSp Mw.wt.ρ Mw.J Mw.χ := fun y => by
    rw [← Mw.real_range]; exact LinearMap.mem_range_self _ y
  have hRJ : Function.Injective fun x => Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) x) :=
    Mw.real_inj.comp (Formalism.L2.jMt_injective _ _)
  have htN0 : NG.tN Mw.J s0 ϖ0 k (0 : GAf D.host.E D.R.nV → Mw.wt.W) = 0 := by
    have := Plin (0 : GAf D.host.E D.R.nV → Mw.wt.W) (Submodule.zero_mem _) 0 (Submodule.zero_mem _) 1
    rw [one_smul, add_zero, one_smul] at this
    simpa using this
  let T0 : D.what₂.MtL (D.what₂.muTw w) (j' + 1) → D.what₂.MtL (D.what₂.muTw w) (j' + 1) := fun x => (hrat x).choose
  have hT0 : ∀ x, Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) (T0 x)) =
      NG.tN Mw.J s0 ϖ0 k (Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) x)) := fun x => (hrat x).choose_spec
  have hadd : ∀ x y, T0 (x + y) = T0 x + T0 y := by
    intro x y
    apply hRJ
    show Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) (T0 (x + y))) =
      Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) (T0 x + T0 y))
    have := Plin _ (hTS (D.what₂.jMt (D.what₂.muTw w) (j' + 1) x)) _ (hTS (D.what₂.jMt (D.what₂.muTw w) (j' + 1) y)) 1
    rw [one_smul, one_smul] at this
    rw [hT0, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hT0, hT0, this]
  have hsmul : ∀ (a : D.what₂.LL) x, T0 (a • x) = a • T0 x := by
    intro a x
    apply hRJ
    show Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) (T0 (a • x))) =
      Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) (a • T0 x))
    have := Plin _ (hTS (D.what₂.jMt (D.what₂.muTw w) (j' + 1) x)) 0 (Submodule.zero_mem _) (D.what₂.embLL a)
    rw [add_zero, htN0, add_zero] at this
    rw [hT0]
    simp only [LinearMap.map_smulₛₗ, RingHom.id_apply]
    rw [hT0, this]
  let T : Module.End D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) (j' + 1)) :=
    { toFun := T0
      map_add' := hadd
      map_smul' := hsmul }
  refine ⟨T, fun s ϖ hc hu x => ?_⟩
  show Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) (T0 x)) =
    NG.tN Mw.J s ϖ k (Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) x))
  rw [hT0]
  exact tN_eq_of_conj D Mw.J v s0 s ϖ0 ϖ k hc0 hc hu0 hu _

end GlobalTheory.HeckeLiftN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAlgebraicSetHeckeFieldsSplit
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section
namespace GlobalTheory.Mem.HFld.Transp
open _root_.Formalism.L2.Col Polynomial

theorem chiC_apply {B : Base} {px : PreX B.toPre} (I : Col2.ColIn B px) (j : Fin B.R.m)
    (w : {w // w ∈ (B.primes px).vGs}) (y : 𝓞 B.host.E) (hu : IsUnit (Ideal.Quotient.mk w.1.asIdeal y)) :
    chiC I j w.1 y = B.embLL ((I.Ch.chi j w hu.unit : B.LLˣ) : B.LL) := by
  unfold chiC
  rw [dite_eq_left w.2, dite_eq_left hu]

theorem qC_xi {B : Base} {px : PreX B.toPre} {I : Col2.ColIn B px} (hI : I.Ok) (a : I.ι) : qC I (I.xi a) = I.Q a := by
  unfold qC
  rw [dite_eq_left ⟨a, rfl⟩]
  congr 1
  exact hI.xi_inj (Exists.choose_spec (⟨a, rfl⟩ : ∃ a', I.xi a' = I.xi a))

theorem rowTyQ_congr {X : Fields} (R : Ranks) {ξ ξ' : Chr X.F X.E X.K} (h : ξ = ξ')
    {Q Q' : Finset (HeightOneSpectrum (𝓞 X.E))} (Pp : Q) (hp : Pp.1 ∈ Q') :
    rowTyQ R ξ Q Pp = rowTyQ R ξ' Q' ⟨Pp.1, hp⟩ := by
  subst h
  rfl

theorem mtTyQ_congr {X : Fields} (R : Ranks) {ξ ξ' : Chr X.F X.E X.K} (h : ξ = ξ')
    {Q Q' : Finset (HeightOneSpectrum (𝓞 X.E))} (Pp : Q) (hp : Pp.1 ∈ Q') :
    mtTyQ R ξ Q Pp = mtTyQ R ξ' Q' ⟨Pp.1, hp⟩ := by
  subst h
  rfl

set_option maxHeartbeats 6000000 in
theorem core (B0 : Base) (px0 : PreX B0.toPre) (I0 : Col2.ColIn B0 px0) (B : Base) (px : PreX B.toPre)
    (I : Col2.ColIn B px) (hX0 : B0.fields.Ok) (hI0 : I0.Ok) (hI : I.Ok) (hcfg : SameCfg B px I B0 px0 I0)
    (ι : B0.LL →+* B.LL) (hι : B.embLL.comp ι = B0.embLL) (a : I.ι) :
    ∃ a0 : I0.ι, (∀ p : B0.LL[X], HeckePolyFor (heckeFamAll (rowPts B0.wts I0.Ch I0.sel (I0.tup a0)) ∅) p →
        (p.map ι).Splits → HeckeFieldsInAll (rowPts B.wts I.Ch I.sel (I.tup a)) ∅) ∧
      ∀ j : Fin B.R.m, ∀ p : B0.LL[X],
        HeckePolyFor (heckeFamAll (liftPts B0.wts I0.Ch I0.sel (I0.tup a0) (j.1 + 1)) ∅) p →
        (p.map ι).Splits → HeckeFieldsInAll (liftPts B.wts I.Ch I.sel (I.tup a) (j.1 + 1)) ∅ := by
  obtain ⟨hP, -, hXi, hpiG, hchi, hq⟩ := hcfg
  have hQa := qC_xi hI a
  have hxr := hI.xi_reads a
  have hchiA := chiC_apply I
  obtain ⟨P, LL, embLL, hcx, embE, hφ, LL0, _, Ks, _, _, _, _, _, _, _, _⟩ := B
  obtain ⟨P0, LL', embLL', hcx', embE', hφ', LL0', g0, Ks', k1, k2, k3, k4, k5, k6, k7, k8⟩ := B0
  obtain rfl : P = P0 := hP
  change LL' →+* LL at ι
  have hι' : ∀ x, embLL (ι x) = embLL' x := fun x => RingHom.congr_fun hι x
  have hE : embE = ι.comp embE' := by
    ext x
    apply embLL.injective
    have h1 := RingHom.congr_fun hφ x
    have h2 := RingHom.congr_fun hφ' x
    simp only [RingHom.comp_apply] at h1 h2 ⊢
    rw [h1, hι', h2]
  subst hE
  obtain ⟨piG, _, _, _, piT, _, _, _, _, _, _, _, _, _, _, _, _⟩ := px
  obtain ⟨piG', _, _, _, piT', _, _, _, _, _, _, _, _, _, _, _, _⟩ := px0
  obtain rfl : piG = piG' := eq_of_heq hpiG
  have hXi' := eq_of_heq hXi
  obtain ⟨a0, ha0⟩ : ∃ a0, I0.xi a0 = I.xi a := by
    have h : I.xi a ∈ Set.range I.xi := ⟨a, rfl⟩
    rw [hXi'] at h
    exact h
  have hQ : I.Q a = I0.Q a0 := by
    rw [← hQa, ← qC_xi hI0 a0, ha0]
    exact congrFun (eq_of_heq hq) _
  have htup : (I.tup a).1 = chrMap ι (I0.tup a0).1 := by
    refine hxr.inj ?_
    intro x
    rw [← ha0]
    refine (hI0.xi_reads a0 x).trans ?_
    exact (hι' _).symm
  have hchi' := eq_of_heq hchi
  have hch : ∀ (j : Fin P.R.m) w, I.Ch.chi j w = (Units.map ι.toMonoidHom).comp (I0.Ch.chi j w) := by
    intro j w
    ext u
    apply embLL.injective
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (u : 𝓞 P.host.E ⧸ w.1.asIdeal)
    have hu : IsUnit (Ideal.Quotient.mk w.1.asIdeal y) := hy ▸ u.isUnit
    have hu' : hu.unit = u := Units.ext (by rw [IsUnit.unit_spec]; exact hy)
    have h1 := congrFun (congrFun (congrFun hchi' j) w.1) y
    rw [hchiA j w y hu, chiC_apply I0 j w y hu, hu'] at h1
    refine h1.trans ?_
    exact (hι' _).symm
  let B0' : Base := ⟨P, LL', embLL', hcx', embE', hφ', LL0', g0, Ks', k1, k2, k3, k4, k5, k6, k7, k8⟩
  have hQ' : QE I.sel (I.tup a).1 = QE I0.sel (I0.tup a0).1 := hQ
  have hca : ∀ w s, chiAt I.Ch w s = (Units.map ι.toMonoidHom).comp (chiAt I0.Ch w s) := by
    intro w s
    unfold chiAt
    rw [← extChi_coefMap]
    exact congrArg (fun f => extChi f s) (funext fun j => hch j w)
  have hA : rowTyK (R := P.R) I.Ch = (rowTyK (R := P.R) I0.Ch).coefMap ι := by
    funext w
    exact congrArg (Lev.mk (HKJ (𝓞 P.host.E ⧸ w.1.asIdeal) (P.R.N P.R.m - 1) P.R.r P.R.t P.R.m))
      ((congrArg (fun χ => lamK χ (P.R.N P.R.m - 1) P.R.r (List.replicate P.R.m P.R.t)) (funext (hca w))).trans
        (lamK_coefMap ι _ _ _))
  have hAm : ∀ k, mtTyK (R := P.R) I.Ch k = (mtTyK (R := P.R) I0.Ch k).coefMap ι := by
    intro k
    funext w
    have h : (fun _ : ℕ => (chiAt I.Ch w (k - 1))⁻¹) =
        fun _ : ℕ => (Units.map ι.toMonoidHom).comp (chiAt I0.Ch w (k - 1))⁻¹ :=
      funext fun _ => (congrArg (·⁻¹) (hca w (k - 1))).trans (coefMap_comp_inv ι _)
    exact congrArg (Lev.mk (HKV (𝓞 P.host.E ⧸ w.1.asIdeal) P.R.nV P.R.r P.R.t))
      ((congrArg (fun χ => lamK χ P.R.nV P.R.r [P.R.t]) h).trans (lamK_coefMap ι _ _ _))
  have hB : ∀ Pp : {Pp // Pp ∈ QE I.sel (I.tup a).1},
      rowTyQ P.R (I.tup a).1 (QE I.sel (I.tup a).1) Pp =
        (rowTyQ P.R (I0.tup a0).1 (QE I0.sel (I0.tup a0).1) ⟨Pp.1, hQ' ▸ Pp.2⟩).coefMap ι := by
    intro Pp
    rw [← rowTyQ_coefMap (L := LL) (ι := ι) P.R (I0.tup a0) (QE I0.sel (I0.tup a0).1) ⟨Pp.1, hQ' ▸ Pp.2⟩]
    exact rowTyQ_congr P.R htup Pp _
  have hBm : ∀ Pp : {Pp // Pp ∈ QE I.sel (I.tup a).1},
      mtTyQ P.R (I.tup a).1 (QE I.sel (I.tup a).1) Pp =
        (mtTyQ P.R (I0.tup a0).1 (QE I0.sel (I0.tup a0).1) ⟨Pp.1, hQ' ▸ Pp.2⟩).coefMap ι := by
    intro Pp
    rw [← mtTyQ_coefMap (L := LL) (ι := ι) P.R (I0.tup a0) (QE I0.sel (I0.tup a0).1) ⟨Pp.1, hQ' ▸ Pp.2⟩]
    exact mtTyQ_congr P.R htup Pp _
  have hTy : rowTyKK (R := P.R) I.Ch I.sel (I.tup a) =
      ((rowTyKK (R := P.R) I0.Ch I0.sel (I0.tup a0)).coefMap ι).reidx (congrArg (uSG _) hQ') :=
    LevFam.glue_coefMap_reidx ι hQ' _ _ _ _ hA hB
  have hTyL : ∀ k, mtTyKK (R := P.R) I.Ch I.sel (I.tup a) k =
      ((mtTyKK (R := P.R) I0.Ch I0.sel (I0.tup a0) k).coefMap ι).reidx (congrArg (uSG _) hQ') := fun k =>
    LevFam.glue_coefMap_reidx ι hQ' _ _ _ _ (hAm k) hBm
  refine ⟨a0, fun p hp hsp => ?_, fun j p hp hsp => ?_⟩
  · unfold HeckeFieldsInAll rowPts mtildeKGSD at *
    rw [hTy]
    have hfd := GSD.finiteDimensional_EqFun _ (mtildeKOk B0'.wts I0.Ch I0.sel (I0.tup a0) hX0)
    have key := hfs_splitAll_sq_reidx (X := B0'.fields) (L := LL) ι (congrArg (uSG _) hQ') B0'.wts.sgTrue
      (rowTyKK (R := P.R) I0.Ch I0.sel (I0.tup a0)) ∅ hfd (GlobalTheory.InertSame.heckeCommAll_all _ _) hp hsp
    exact key
  · unfold HeckeFieldsInAll liftPts mtKGSD at *
    rw [hTyL]
    have hfd := GSD.finiteDimensional_EqFun _ (mtKOk B0'.wts I0.Ch I0.sel (I0.tup a0) hX0 (j.1 + 1))
    have key := hfs_splitAll_rd_reidx (X := B0'.fields) (L := LL) ι (congrArg (uSG _) hQ') (B0'.wts.lamV (j.1 + 1))
      (mtTyKK (R := P.R) I0.Ch I0.sel (I0.tup a0) (j.1 + 1)) ∅ hfd (GlobalTheory.InertSame.heckeCommAll_all _ _) hp hsp
    exact key

theorem splits_of_roots_mem {K L : Type} [Field K] [Field L] (σ0 : K →+* ℂ) (σ : L →+* ℂ) (ι : K →+* L)
    (hι : σ.comp ι = σ0) (p : K[X]) (hr : ∀ z ∈ (p.map σ0).roots, ∃ y, σ y = z) : (p.map ι).Splits := by
  refine Polynomial.Splits.of_splits_map σ ?_ ?_
  · rw [Polynomial.map_map, hι]
    exact IsAlgClosed.splits _
  · intro z hz
    rw [Polynomial.map_map, hι] at hz
    obtain ⟨y, hy⟩ := hr z hz
    exact ⟨y, hy⟩

theorem transp : ∀ (B0 : Base) (px0 : PreX B0.toPre) (I0 : Col2.ColIn B0 px0), B0.fields.Ok → I0.Ok →
  ∃ s : Finset ℂ, (∀ z ∈ s, IsAlgebraic ℚ z) ∧
    ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px), B.fields.Ok → I.Ok → GlobalTheory.Mem.HFld.SameCfg B px I B0 px0 I0 →
      (∀ z ∈ s, z ∈ B.LLC) → ∀ a : I.ι,
        Formalism.L2.Col.HeckeFieldsInAll (rowPts B.wts I.Ch I.sel (I.tup a)) ∅ ∧
          ∀ j : Fin B.R.m, Formalism.L2.Col.HeckeFieldsInAll (liftPts B.wts I.Ch I.sel (I.tup a) (j.1 + 1)) ∅ := by
  intro B0 px0 I0 hX0 hI0
  classical
  have hR : ∀ a0 : I0.ι, ∃ p, HeckePolyFor (heckeFamAll (rowPts B0.wts I0.Ch I0.sel (I0.tup a0)) ∅) p := fun a0 => by
    haveI := GSD.finiteDimensional_EqFun _ (mtildeKOk B0.wts I0.Ch I0.sel (I0.tup a0) hX0)
    exact hfs_exists_poly _
  have hL : ∀ (a0 : I0.ι) (k : ℕ), ∃ p, HeckePolyFor (heckeFamAll (liftPts B0.wts I0.Ch I0.sel (I0.tup a0) k) ∅) p :=
    fun a0 k => by
      haveI := GSD.finiteDimensional_EqFun _ (mtKOk B0.wts I0.Ch I0.sel (I0.tup a0) hX0 k)
      exact hfs_exists_poly _
  choose pR hpR using hR
  choose pL hpL using hL
  let bas := Module.finBasis ℚ B0.LL
  let rts : B0.LL[X] → Finset ℂ := fun p => (p.map B0.embLL).roots.toFinset
  let s : Finset ℂ := Finset.univ.image (fun i => B0.embLL (bas i)) ∪
    Finset.univ.biUnion (fun a0 : I0.ι => rts (pR a0) ∪ (Finset.range B0.R.m).biUnion (fun k => rts (pL a0 (k + 1))))
  have hrts : ∀ p : B0.LL[X], p ≠ 0 → ∀ z ∈ rts p, IsAlgebraic ℚ z := by
    intro p hp z hz
    letI : Algebra B0.LL ℂ := B0.embLL.toAlgebra
    haveI : IsScalarTower ℚ B0.LL ℂ := IsScalarTower.of_algebraMap_eq fun q => by simp
    have h1 : IsAlgebraic B0.LL z := ⟨p, hp, by
      have h2 : z ∈ (p.map B0.embLL).roots := Multiset.mem_toFinset.1 hz
      rw [Polynomial.mem_roots (Polynomial.map_ne_zero hp)] at h2
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
      exact h2⟩
    exact h1.restrictScalars ℚ
  refine ⟨s, ?_, ?_⟩
  · intro z hz
    rcases Finset.mem_union.1 hz with h | h
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
      exact (isAlgebraic_algHom_iff B0.embLL.toRatAlgHom B0.embLL.injective).2 (Algebra.IsAlgebraic.isAlgebraic _)
    · obtain ⟨a0, -, h⟩ := Finset.mem_biUnion.1 h
      rcases Finset.mem_union.1 h with h | h
      · exact hrts _ (hpR a0).1 z h
      · obtain ⟨k, -, h⟩ := Finset.mem_biUnion.1 h
        exact hrts _ (hpL a0 (k + 1)).1 z h
  · intro B px I hX hI hcfg hs a
    have hm : B.R.m = B0.R.m := congrArg (fun P : Pre => P.R.m) hcfg.1
    have hLL : ∀ x : B0.LL, ∃ y : B.LL, B.embLL y = B0.embLL x := by
      intro x
      have hb : ∀ i, B0.embLL (bas i) ∈ B.LLC := fun i =>
        hs _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
      have hx : B0.embLL x ∈ B.LLC := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← bas.sum_repr x, map_sum]
        refine sum_mem fun i _ => ?_
        rw [map_rat_smul]
        exact SMulMemClass.smul_mem _ (hb i)
      exact hx
    choose f hf using hLL
    let ι : B0.LL →+* B.LL :=
      { toFun := f
        map_one' := B.embLL.injective (by rw [hf, map_one, map_one])
        map_mul' := fun x y => B.embLL.injective (by rw [hf, map_mul, map_mul, hf, hf])
        map_zero' := B.embLL.injective (by rw [hf, map_zero, map_zero])
        map_add' := fun x y => B.embLL.injective (by rw [hf, map_add (f := _), map_add (f := _), hf, hf]) }
    have hι : B.embLL.comp ι = B0.embLL := RingHom.ext hf
    have hsp : ∀ p : B0.LL[X], (∀ z ∈ rts p, z ∈ s) → (p.map ι).Splits := fun p hp =>
      splits_of_roots_mem B0.embLL B.embLL ι hι p fun z hz => hs z (hp z (Multiset.mem_toFinset.2 hz))
    obtain ⟨a0, hrow, hlift⟩ := core B0 px0 I0 B px I hX0 hI0 hI hcfg ι hι a
    refine ⟨hrow (pR a0) (hpR a0) (hsp _ fun z hz => ?_), fun j => hlift j (pL a0 (j.1 + 1)) (hpL a0 (j.1 + 1))
      (hsp _ fun z hz => ?_)⟩
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨a0, Finset.mem_univ _, Finset.mem_union_left _ hz⟩)
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨a0, Finset.mem_univ _, Finset.mem_union_right _ ?_⟩)
      exact Finset.mem_biUnion.2 ⟨j.1, Finset.mem_range.2 (hm ▸ j.2), hz⟩

end GlobalTheory.Mem.HFld.Transp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntOfFinite
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtIn

theorem exists_int_of_finite {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {G : Type} [Group G] [Finite G]
    (f : G →* ℂˣ) (g : G) (h : ∃ y : K, σ y = ((f g : ℂˣ) : ℂ)) : ∃ z : 𝓞 K, σ (z : K) = ((f g : ℂˣ) : ℂ) := by
  obtain ⟨y, hy⟩ := h
  have hn : 0 < Nat.card G := Nat.card_pos
  have hfg : (f g) ^ Nat.card G = 1 := by rw [← map_pow, pow_card_eq_one', map_one]
  have hy1 : y ^ Nat.card G = 1 := by
    apply σ.injective
    rw [map_pow, hy, map_one, ← Units.val_pow_eq_pow_val, hfg, Units.val_one]
  have hint : IsIntegral ℤ y := IsIntegral.of_pow hn (by rw [hy1]; exact isIntegral_one)
  exact ⟨⟨y, hint⟩, hy⟩

end GlobalTheory.MtIn


open GlobalTheory.MtIn in
theorem GlobalTheory.MtIn.levChi_integral : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → LevOf X I U L → ∀ (i : Fin X.toD7.R.m) (t : TupU I U) (k : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J), ∃ z : 𝓞 X.toD7.what₂.LL, X.toD7.what₂.embLL (z : X.toD7.what₂.LL) = ((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).χ k : ℂ) := by
  intro X px I U L hI hL i t k
  have hfin : ∀ PP : Pl X.toD7.host.E, Finite (kP PP)ˣ := fun PP =>
    haveI : Finite (kP PP) := Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
    Finite.of_injective _ Units.val_injective
  have lift : ∀ (PP : Pl X.toD7.host.E) (d : (kP PP)ˣ), ∃ (a : 𝓞 X.toD7.host.E) (kE : X.toD7.host.Eˣ),
      (kE : X.toD7.host.E) = a ∧ (d : kP PP) = Ideal.Quotient.mk _ a := by
    intro PP d
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (d : kP PP)
    have ha0 : (a : X.toD7.host.E) ≠ 0 := by
      intro h0
      have : a = 0 := by exact_mod_cast h0
      apply d.ne_zero
      rw [← ha, this, map_zero]
    exact ⟨a, Units.mk0 _ ha0, rfl, ha.symm⟩
  have hchi : ∀ PP ∈ L.Pg, ∀ d : (kP PP)ˣ, ∃ y, X.toD7.what₂.embLL y = (((L.chi ((i : ℕ) + 1) PP)⁻¹ d : ℂˣ) : ℂ) := by
    intro PP hPP d
    obtain ⟨a, kE, h1, h2⟩ := lift PP d
    have hres := hL.is.chi i PP hPP a kE d h1 h2
    rw [hres, hL.C]
    have hw : PP ∈ (X.B.primes px).vGs := hL.Pg ▸ hPP
    exact ⟨_, ((hI.ch_tied.mu0 i).atg ⟨PP, hw⟩ kE a d h1 h2).symm⟩
  have hxi : ∀ PP ∈ L.Q t, ∀ d : (kP PP)ˣ, ∃ y, X.toD7.what₂.embLL y = ((L.xiR t PP d : ℂˣ) : ℂ) := by
    intro PP hPP d
    obtain ⟨a, kE, h1, h2⟩ := lift PP d
    have hres := hL.is.xiR t PP hPP a kE d h1 h2
    rw [hres, hL.xiH t]
    exact ⟨_, (hI.xi_reads (ixOf I U t) _).symm⟩
  let Pr : ℂˣ → Prop := fun u => ∃ z : 𝓞 X.toD7.what₂.LL, X.toD7.what₂.embLL (z : X.toD7.what₂.LL) = (u : ℂ)
  have hmul : ∀ a b : ℂˣ, Pr a → Pr b → Pr (a * b) := by
    rintro a b ⟨za, ha⟩ ⟨zb, hb⟩
    exact ⟨za * zb, by rw [Units.val_mul, ← ha, ← hb, ← map_mul]; rfl⟩
  have hone : Pr 1 := ⟨1, by rw [Units.val_one, ← map_one X.toD7.what₂.embLL]; rfl⟩
  have gchi : ∀ PP ∈ L.Pg, ∀ (c : ℕ) (d : (kP PP)ˣ), Pr ((if Frm.A = Frm.B then (fun _ : ℕ => L.chi ((i : ℕ) + 1)) else
      fun (_ : ℕ) (PP : Pl X.toD7.host.E) => (L.chi ((i : ℕ) + 1) PP)⁻¹) c PP d) := by
    intro PP hPP c d
    haveI := hfin PP
    have e : (if Frm.A = Frm.B then (fun _ : ℕ => L.chi ((i : ℕ) + 1)) else fun (_ : ℕ) (PP : Pl X.toD7.host.E) => (L.chi ((i : ℕ) + 1) PP)⁻¹) =
        fun (_ : ℕ) (PP : Pl X.toD7.host.E) => (L.chi ((i : ℕ) + 1) PP)⁻¹ := if_neg (by decide)
    rw [e]
    exact exists_int_of_finite X.toD7.what₂.embLL (L.chi ((i : ℕ) + 1) PP)⁻¹ d (hchi PP hPP d)
  have gxi : ∀ PP ∈ L.Q t, ∀ d : (kP PP)ˣ, Pr ((if Frm.A = Frm.B then (fun PP => (L.xiR t PP)⁻¹) else L.xiR t) PP d) := by
    intro PP hPP d
    haveI := hfin PP
    have e : (if Frm.A = Frm.B then (fun PP => (L.xiR t PP)⁻¹) else L.xiR t) = L.xiR t := if_neg (by decide)
    rw [e]
    exact exists_int_of_finite X.toD7.what₂.embLL (L.xiR t PP) d (hxi PP hPP d)
  show Pr (Formalism.L2.DIV.levFn (L.βV i) (flag1L (L.datVt i t)) _)
  unfold Formalism.L2.DIV.levFn
  refine hmul _ _ (hmul _ _ ?_ (Finset.prod_induction _ Pr hmul hone fun PP hPP =>
    Finset.prod_induction _ Pr hmul hone fun c _ => ?_)) (Finset.prod_induction _ Pr hmul hone fun PP hPP => ?_)
  · unfold Formalism.L2.DIV.ext1
    split_ifs
    · exact hone
    · exact hone
  · exact gchi PP hPP (c + 1) _
  · exact gxi PP hPP _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueCharOfTameCharPrimeResidueFieldStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residue_char_of_tame_char_prime_residue_field : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (P : HeightOneSpectrum (𝓞 E)) (g : ℕ), g.Prime → normV P = g → ((g : ℕ) : 𝓞 E) ∈ P.asIdeal → ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → (∀ A : ValuationSubring Ω, IsPlaceOver A P → ∀ σ ∈ Ine (F := E) A, χ σ ^ (g - 1) = 1) → ∃ τ : (ZMod g)ˣ →* Oˣ, ∀ (x : (ZMod g)ˣ) (u : 𝓞 E), (((x : ZMod g).val : 𝓞 E) - u) ∈ P.asIdeal → τ x = NX.tameVal χ P 1 u := by
  first | exact @GlobalTheory.TameTau.tameChar_of_prime_residue | exact GlobalTheory.TameTau.tameChar_of_prime_residue | (intros; apply GlobalTheory.TameTau.tameChar_of_prime_residue <;> assumption)
end

