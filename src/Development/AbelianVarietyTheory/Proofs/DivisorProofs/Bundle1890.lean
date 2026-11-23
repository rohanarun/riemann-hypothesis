module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1604
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1853
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1684
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1354
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1848
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThFamMono
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CovGmin

def Hyp (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o Lb : ℝ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    Prop :=
  LawsJ T ∧ 1 ≤ (T.Q.Dw j).p ∧ 1 ≤ (T.Q.Dw j).q ∧ 2 < Module.finrank ℚ D.host.E / 2 ∧ InR D j ∧ Y.Good e o ∧
    1 ≤ Lb ∧ Real.log Y.d.l₂.M ≤ 30 * Lb ∧ fieldSz D.host.E ≤ 3 * Lb ∧ Real.log (D.R.f * D.R.r) ≤ Lb ∧
    o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 ∧ Dom a n ∧ Even n ∧ 8 * D.R.f * D.R.r + 4 ≤ n ∧
    (∀ (τ : Psi T.Q.H) (k : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (k : ℕ) < (T.Q.Dw j).p →
      ((n / 2 : ℕ) : ℤ) < laOf (T.Q.Dw j) a n τ k) ∧
    Real.log (sizeK (T.Q.Dw j) a n) ≤ 20 * Lb

def badC {D : D7} {T : Core D} {j : ℕ} (Y : Deep T j) : ℕ := D.host.QS * D.host.q * D.host.d * Y.d.l₂.M

def thFam {D : D7} {T : Core D} {j : ℕ} (Y : Deep T j) (nab : NabV Y.d.Xo₂ Y.d.c₂) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (n : ℕ) (ρ : ℝ) : Set (Y.V (wtZ a n)) :=
  {y | ∃ (x0 : Fin n → LevQc (T.Q.Dw j) Y.d.l₂) (La : GenLat D.host.E n) (N : ℕ)
      (P : MvPolynomial (LtN (T.Q.Dw j) n) Y.d.c₂.F),
    Submodule.span (𝓞 D.host.E) (Set.range x0) = ⊤ ∧ La.Unimod ∧ La.TrivAt (badC Y) ∧ La.TrivAt Y.d.l₂.M ∧
      La.LevOK N Y.d.l₂.M ∧ P ∈ harmL Y.d.c₂ La a ∧ GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightData.polyNorm Y.d.c₂ P ≤ ρ ∧
      ∀ (p : TRing Y.d.c₂.F) (y' : FrPt Y.d.Xo₂ Y.d.c₂ p.R),
        thLaValAt Y.d.Xo₂ Y.d.c₂ nab (phiHat Y.d.c₂ (indPhi Y.d.c₂ x0)) La N P y' ((y : Rul Y.d.Xo₂ Y.d.c₂) p y')}

end GlobalTheory.CovGmin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExponentsDominantLastEntryOneDegree
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RefSum

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H}

theorem conjEmb_rt_of_not {τ : E →+* ℂ} (h : ¬ τ (H.rt : E) = H.rt0) :
    conjEmb τ (H.rt : E) = H.rt0 := by
  have hE : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
    simpa using this
  have hsq : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow, hE]; simp
  have hneg : τ (H.rt : E) = -H.rt0 := (sq_eq_sq_iff_eq_or_eq_neg.1 hsq).resolve_left h
  have hre : H.rt0.re = 0 := by
    have h2 := H.sqrt_neg_disc_sq
    have hr := congrArg Complex.re h2
    have hi := congrArg Complex.im h2
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im] at hr hi
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    by_contra hne
    have him : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [him] at hr
    nlinarith [mul_self_nonneg H.rt0.re]
  show (starRingEnd ℂ) (τ (H.rt : E)) = H.rt0
  rw [hneg]
  apply Complex.ext <;> simp [hre]

theorem psi_or_conj (σ : E →+* ℂ) : (∃ τ : Psi H, σ = τ.1) ∨ ∃ τ : Psi H, σ = conjEmb τ.1 := by
  by_cases h : σ (H.rt : E) = H.rt0
  · exact Or.inl ⟨⟨σ, h⟩, rfl⟩
  · exact Or.inr ⟨⟨conjEmb σ, conjEmb_rt_of_not h⟩, (GlobalTheory.AllWt.conjEmb_conjEmb σ).symm⟩

theorem psi_nonempty : Nonempty (Psi H) := by
  have : 0 < Fintype.card (E →+* ℂ) := by
    rw [NumberField.Embeddings.card]; exact Module.finrank_pos
  obtain ⟨σ⟩ := Fintype.card_pos_iff.1 this
  rcases psi_or_conj (H := H) σ with ⟨τ, -⟩ | ⟨τ, -⟩ <;> exact ⟨τ⟩

theorem sum_mult : ∑ τ : E →+* ℂ, Dw.mult τ = (Module.finrank ℚ E / 2) * (Dw.p + Dw.q) := by
  classical
  set P := (Finset.univ : Finset (E →+* ℂ)).filter (fun τ => τ (H.rt : E) = H.rt0) with hP
  set Q := (Finset.univ : Finset (E →+* ℂ)).filter (fun τ => ¬ τ (H.rt : E) = H.rt0) with hQ
  have hcard : Q.card = P.card := by
    refine Finset.card_nbij' conjEmb conjEmb ?_ ?_ ?_ ?_
    · intro a ha
      simp only [hQ, hP, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢
      exact conjEmb_rt_of_not ha
    · intro a ha
      simp only [hQ, hP, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢
      exact GlobalTheory.AllWt.conj_not_mem ⟨a, ha⟩
    · intro a _; exact GlobalTheory.AllWt.conjEmb_conjEmb a
    · intro a _; exact GlobalTheory.AllWt.conjEmb_conjEmb a
  have htot : P.card + Q.card = Module.finrank ℚ E := by
    rw [← NumberField.Embeddings.card E ℂ, ← Finset.card_univ]
    exact Finset.card_filter_add_card_filter_not _
  have hsum : ∑ τ : E →+* ℂ, Dw.mult τ = P.card * Dw.p + Q.card * Dw.q := by
    simp only [Datum.mult]
    rw [Finset.sum_ite]
    simp [Finset.sum_const, hP, hQ]
  rw [hsum, hcard, ← htot, hcard, ← two_mul, Nat.mul_div_cancel_left _ (by norm_num)]
  ring


variable (Dw) in
abbrev thExpZ (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) : (E →+* ℂ) × ℕ → ℤ :=
  (GlobalTheory.AllWt.wtOf Dw (u + GlobalTheory.FlatLine.parWt Dw (shift Dw u n)) ((n / 2 : ℕ) : ℤ)).1

theorem thExpZ_big (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) (τ : Psi H) (i : ℕ) (hi : i < Dw.p) :
    thExpZ Dw u n (τ.1, i) = u τ ⟨i, by omega⟩ + 1 - u τ ⟨Dw.p - 1, by omega⟩ := by
  rw [thExpZ, GlobalTheory.AllWt.wtOf_big _ _ τ i hi]
  simp only [Pi.add_apply, GlobalTheory.FlatLine.parWt, shift, dif_pos (show 0 < Dw.p by omega)]
  ring

theorem thExpZ_big_ge (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) (τ : Psi H) (i : ℕ) (hi : Dw.p ≤ i) :
    thExpZ Dw u n (τ.1, i) = 0 := by
  simp only [thExpZ, GlobalTheory.AllWt.wtOf, dif_pos τ.2, dif_neg (not_lt.2 hi)]

theorem thExpZ_small (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) (hp : 0 < Dw.p) (τ : Psi H) (i : ℕ) (hi : i < Dw.q) :
    thExpZ Dw u n (conjEmb τ.1, i) =
      u τ ⟨Dw.p - 1, by omega⟩ - u τ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ - 2 * ((n / 2 : ℕ) : ℤ) - 1 := by
  rw [thExpZ, GlobalTheory.AllWt.wtOf_small _ _ τ i hi]
  simp only [Pi.add_apply, GlobalTheory.FlatLine.parWt, shift, dif_pos hp]
  ring

theorem thExpZ_small_ge (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) (τ : Psi H) (i : ℕ) (hi : Dw.q ≤ i) :
    thExpZ Dw u n (conjEmb τ.1, i) = 0 := by
  have h' : conjEmb (conjEmb τ.1) (H.rt : E) = H.rt0 := by
    rw [GlobalTheory.AllWt.conjEmb_conjEmb]; exact τ.2
  simp only [thExpZ, GlobalTheory.AllWt.wtOf, dif_neg (GlobalTheory.AllWt.conj_not_mem τ), dif_pos h', dif_neg (not_lt.2 hi)]

theorem thA_dominant_lastPos_degree (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) (b : ℝ) (hp : 1 ≤ Dw.p)
    (hn : Even n) (hu : ∀ τ, Antitone (u τ))
    (hgap : ∀ τ (i j : Fin (Dw.p + Dw.q)), (i : ℕ) + 1 = Dw.p → (j : ℕ) = Dw.p → (n : ℤ) + 1 ≤ u τ i - u τ j)
    (hb : ∀ τ i, |(u τ i : ℝ)| ≤ b) :
    Formalism.L2.Pj.Dom (thA Dw u n) n ∧
      Formalism.L2.Pj.wtZ (thA Dw u n) n =
        GlobalTheory.AllWt.wtOf Dw (u + GlobalTheory.FlatLine.parWt Dw (shift Dw u n)) ((n / 2 : ℕ) : ℤ) ∧
      Formalism.L2.Pj.LastPos Dw (thA Dw u n) ∧ (∀ x, (thA Dw u n x : ℝ) ≤ 2 * b + 1) ∧
      (Formalism.L2.Pj.DF Dw (thA Dw u n) : ℝ) ≤ (Module.finrank ℚ E / 2 : ℕ) * (Dw.p + Dw.q : ℕ) * (2 * b + 1) := by
  have hp0 : 0 < Dw.p := hp
  obtain ⟨τ0⟩ := psi_nonempty (H := H)
  have hb0 : 0 ≤ b := (abs_nonneg _).trans (hb τ0 ⟨0, by omega⟩)
  have hup : ∀ τ i, (u τ i : ℝ) ≤ b := fun τ i => (le_abs_self _).trans (hb τ i)
  have hlo : ∀ τ i, -b ≤ (u τ i : ℝ) := fun τ i => by
    have := neg_abs_le (u τ i : ℝ); linarith [hb τ i]
  have hm : 2 * ((n / 2 : ℕ) : ℤ) = n := by obtain ⟨k, rfl⟩ := hn; omega

  have F1 : ∀ x, 0 ≤ thExpZ Dw u n x := by
    rintro ⟨σ, i⟩
    rcases psi_or_conj (H := H) σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
    · by_cases hi : i < Dw.p
      · rw [thExpZ_big u n τ i hi]
        have := hu τ (show (⟨i, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨Dw.p - 1, by omega⟩ from Fin.mk_le_mk.2 (by omega))
        omega
      · rw [thExpZ_big_ge u n τ i (by omega)]
    · by_cases hi : i < Dw.q
      · rw [thExpZ_small u n hp0 τ i hi]
        have h1 := hu τ (show (⟨Dw.p, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ from
          Fin.mk_le_mk.2 (by omega))
        have h2 := hgap τ ⟨Dw.p - 1, by omega⟩ ⟨Dw.p, by omega⟩ (by simp; omega) rfl
        omega
      · rw [thExpZ_small_ge u n τ i (by omega)]

  have F2 : ∀ x, (thExpZ Dw u n x : ℝ) ≤ 2 * b + 1 := by
    rintro ⟨σ, i⟩
    rcases psi_or_conj (H := H) σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
    · by_cases hi : i < Dw.p
      · rw [thExpZ_big u n τ i hi]; push_cast
        linarith [hup τ ⟨i, by omega⟩, hlo τ ⟨Dw.p - 1, by omega⟩]
      · rw [thExpZ_big_ge u n τ i (by omega)]; push_cast; linarith
    · by_cases hi : i < Dw.q
      · rw [thExpZ_small u n hp0 τ i hi, hm]; push_cast
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
        linarith [hup τ ⟨Dw.p - 1, by omega⟩, hlo τ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩]
      · rw [thExpZ_small_ge u n τ i (by omega)]; push_cast; linarith

  have F3 : ∀ σ i, thExpZ Dw u n (σ, i + 1) ≤ thExpZ Dw u n (σ, i) := by
    intro σ i
    rcases psi_or_conj (H := H) σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
    · by_cases hi : i + 1 < Dw.p
      · rw [thExpZ_big u n τ _ hi, thExpZ_big u n τ i (by omega)]
        have := hu τ (show (⟨i, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨i + 1, by omega⟩ from Fin.mk_le_mk.2 (by omega))
        omega
      · rw [thExpZ_big_ge u n τ (i + 1) (by omega)]; exact F1 _
    · by_cases hi : i + 1 < Dw.q
      · rw [thExpZ_small u n hp0 τ _ hi, thExpZ_small u n hp0 τ i (by omega)]
        have := hu τ (show (⟨Dw.p + (Dw.q - 1 - (i + 1)), by omega⟩ : Fin (Dw.p + Dw.q)) ≤
          ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ from Fin.mk_le_mk.2 (by omega))
        omega
      · rw [thExpZ_small_ge u n τ (i + 1) (by omega)]; exact F1 _
  have hcast : ∀ x, (thA Dw u n x : ℝ) = (thExpZ Dw u n x : ℝ) := fun x => by
    have h := Int.toNat_of_nonneg (F1 x)
    show (((thExpZ Dw u n x).toNat : ℕ) : ℝ) = _
    rw [← h]; norm_cast
  have hbound : ∀ x, (thA Dw u n x : ℝ) ≤ 2 * b + 1 := fun x => (hcast x).trans_le (F2 x)
  refine ⟨⟨fun σ => antitone_nat_of_succ_le fun i => Int.toNat_le_toNat (F3 σ i), hn⟩, ?_, ?_, hbound, ?_⟩
  · refine Prod.ext (funext fun x => ?_) ?_
    · exact Int.toNat_of_nonneg (F1 x)
    · show (n : ℤ) = 2 * ((n / 2 : ℕ) : ℤ)
      omega
  · intro σ hσ _
    have hmul : Dw.mult σ = Dw.p := if_pos hσ
    rw [hmul]
    have h1 : thExpZ Dw u n (σ, Dw.p - 1) = 1 :=
      (thExpZ_big u n ⟨σ, hσ⟩ (Dw.p - 1) (by omega)).trans (by ring)
    show 0 < (thExpZ Dw u n (σ, Dw.p - 1)).toNat
    rw [h1]; decide
  · have hDF : (Formalism.L2.Pj.DF Dw (thA Dw u n) : ℝ) ≤ ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (2 * b + 1) := by
      unfold Formalism.L2.Pj.DF; push_cast
      refine Finset.sum_le_sum fun τ _ => ?_
      calc ∑ i : Fin (Dw.mult τ), (thA Dw u n (τ, i) : ℝ) ≤ ∑ _i : Fin (Dw.mult τ), (2 * b + 1) :=
            Finset.sum_le_sum fun i _ => hbound (τ, i)
        _ = _ := by simp [mul_add]
    rw [← Finset.sum_mul] at hDF
    have hs : (∑ τ : E →+* ℂ, (Dw.mult τ : ℝ)) =
        ((Module.finrank ℚ E / 2 : ℕ) : ℝ) * ((Dw.p + Dw.q : ℕ) : ℝ) := by
      rw [← Nat.cast_sum, sum_mult, Nat.cast_mul]
    rw [hs] at hDF
    exact hDF

end GlobalTheory.RefSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionNormComplexPointsEqTwoPiPow
section
noncomputable section

namespace GlobalTheory.KeyArchNorm

section Value

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth

theorem norm_rule_of_coord {κ : GlobalTheory.KeyCl.Rule} (hκ : GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ) (x : KeyIn ℂ) {g : ℕ}
    (hg : g = x.P.g) (u : HolUnif x.P.A x.P.L g) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    {θ : (Fin g → ℂ) → ℂ} {Fd : Set (Fin g → ℂ)} {ξ : ℝ} (hξ : 0 < ξ) (p : Fin x.P.g ≃ Fin g)
    (hA : u.IsAH Hm χ) (hR : u.IsRig x.rig) (hF : u.IsFn x.th θ) (hD : ∀ i, u.IsDiff (Pi.single (p i) 1) (x.v i))
    (hFd : IsAddFundamentalDomain u.Λ Fd volume)
    (hN : (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal = 1)
    (hH : Hm = ((2 * ξ : ℝ) : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ)) :
    ‖(κ ℂ x : ℂ)‖ = (2 * Real.pi) ^ (2 * g) * (2 * Real.pi * ξ) ^ (2 * g) := by
  subst hg
  obtain ⟨⟨Ef, hE, hb⟩, -⟩ := unimodular_and_tangent_of_isAH thetaUnifAV_all x.P x.rig x.rig_gen u Hm χ hA
  have := u.discrete
  have hv := volume_mul_det_eq_one_of_unimodular _ u.Λ u.full Hm Ef Fd hA.1 hA.2.1 hE hb hFd
  have hd : Hm.det.re = (2 * ξ) ^ x.P.g := by
    rw [hH, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, ← Complex.ofReal_pow, Complex.ofReal_re]
  let W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ := Matrix.of fun i => Pi.single (p i) 1
  have hW : ‖W.det‖ = 1 := by
    have e : W = (1 : Matrix (Fin x.P.g) (Fin x.P.g) ℂ).submatrix p id := by
      ext i j
      simp [W, Pi.single_apply, Matrix.one_apply, eq_comm]
    rw [e, Matrix.det_permute, Matrix.det_one, mul_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h | h <;> simp [h]
  have key := hκ x u Hm W χ θ Fd 1 _ hA hR hF hD hFd hN.symm rfl
  rw [hd] at hv
  rw [hW, eq_inv_of_mul_eq_one_left hv] at key
  have hπ := Real.pi_pos
  simp only [mul_one, one_pow] at key
  rw [← key]
  simp only [mul_pow, pow_mul']
  field_simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem norm_rule_of_isOrtho {κ : GlobalTheory.KeyCl.Rule} (hκ : GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {ξ : ℝ} (h0 : 0 < ξ)
    (hσ : GoodEmb c σ) (hU : IsUnf U) (k : U.Comp) (x : (U.X k).dom) (hξ : ∀ τ : E →+* ℂ, ‖τ (U.X k).ξ0‖ = ξ)
    (hx : (U.X k).IsOrtho x.1) (Φ : FibKey Xo ℂ (U.un k x).x)
    (hΦ : Tied (S := ℂ) e (U.un k x).s (U.un k x).u Φ) :
    ‖(κ ℂ Φ.key : ℂ)‖ = (2 * Real.pi) ^ (2 * g) * (2 * Real.pi * ξ) ^ (2 * g) := by
  obtain ⟨ht, hg, hv⟩ := hΦ
  subst hg
  obtain ⟨W⟩ := PullbackSections.nonempty_unfAt hU k x
  obtain ⟨Wu⟩ := PullbackSections.nonempty_unitAt W (PullbackSections.PfSupAtUnit.dmin_ortho _ hx)
  have hH := OrthoHerm.hm_eq_smul_one E H Dw l Xo c σ r U ξ hσ hU k x W Wu hξ hx
  obtain ⟨u, χ, hΛ, hA, hR, hF, hg, hD⟩ := OrthoMetric.exists_unif W.F (W.ik k) W.per W.pt Φ ht Wu.herm Wu.pos Wu.c2
    Wu.c3 Wu.c4 Wu.c5 Wu.c6 Wu.c7
  have hFd : IsAddFundamentalDomain u.Λ Wu.Fd volume := hΛ ▸ Wu.c8
  have key := norm_rule_of_coord hκ Φ.key hg u h0 (e.trans W.e.symm) hA hR hF (fun i => by
    obtain ⟨w, hw, hd⟩ := hD _ _ ((U.un k x).tan (e i).1 (e i).2) (W.der (e i).1 (e i).2)
    have hwv : w = Φ.v i :=
      Over.OverMorphism.ext (Φ.m.cart.1.hom_ext (hw.trans (hv i).symm) ((Over.w w).trans (Over.w (Φ.v i)).symm))
    rw [hwv] at hd
    exact hd) hFd Wu.c9 hH
  rw [hg] at key
  exact key

end Value

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

section Weight

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem wtOf_fst (τ : E →+* ℂ) (i : ℕ) (hi : i < Dw.mult τ) : (wtOf Dw 0 (-4)).1 (τ, i) = 4 := by
  by_cases h : τ (H.rt : E) = H.rt0
  · have hp : i < Dw.p := by simpa [Datum.mult, h] using hi
    rw [wtOf_big _ _ ⟨τ, h⟩ i hp]
    simp
  · have hq : i < Dw.q := by simpa [Datum.mult, h] using hi
    have e := wtOf_small (Dw := Dw) 0 (-4) ⟨conjEmb τ, conj_mem h⟩ i hq
    simp only [conjEmb_conjEmb] at e
    rw [e]
    simp

theorem exZ_wtOf : exZ Dw (wtOf Dw 0 (-4)) = (4 : ℤ) • keyEx Dw := by
  funext i
  rcases i with _ | ⟨τ, i⟩
  · rfl
  · exact wtOf_fst τ i i.2

theorem lieFacZ_mul {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) {x : ℝ} (hx : 0 < x) :
    lieFacZ Dw x (wtOf Dw 0 (-4)) * (2 * Real.pi * x) ^ (2 * g) = 1 := by
  have hg : ∑ τ : E →+* ℂ, Dw.mult τ = g := by
    have := Fintype.card_congr e
    simpa using this.symm
  have hs : (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), ((wtOf Dw 0 (-4)).1 (τ, i) : ℝ)) = 4 * g := by
    rw [← hg, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_congr rfl fun (i : Fin (Dw.mult τ)) _ => by rw [wtOf_fst τ i i.2]]
    simp [mul_comm]
  have hπ : 0 < 2 * Real.pi * x := by positivity
  rw [lieFacZ, hs, ← Real.exp_log (pow_pos hπ (2 * g)), ← Real.exp_add, Real.log_pow, Real.exp_eq_one_iff]
  push_cast
  ring

end Weight

theorem homN_key_const : ∀ (κ : GlobalTheory.KeyCl.Rule), GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (x : ℝ) (K : (Rul Xo c)ˣ), GoodEmb c σ → IsUnf U → (∀ k (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = x) → Nonempty (KeySec Xo c) → 1 ≤ Dw.p + Dw.q → (K : Rul Xo c) ∈ secZ Xo c ((4 : ℤ) • keyEx Dw) → (∀ (F : Type) [Field F] [CharZero F] [Algebra c.F F] (y : FrPt Xo c F) (Φ : FibKey Xo F y.x), Tied e y.s y.u Φ → evR Xo c (K : Rul Xo c) y = (κ F Φ.key : F)) → ∃ C : ℝ, 0 < C ∧ |Real.log C| ≤ 2 * (g : ℝ) * Real.log (2 * Real.pi) ∧ ∀ k, ∀ y ∈ (U.X k).dom, homN U x (wtOf Dw 0 (-4)) (K : Rul Xo c) ⟨k, y⟩ = C := by
  intro κ _ _ hκ E _ _ _ H Dw l Xo c g e σ r U x K hσ hU hx hS hpq hK hval
  have hπ : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  refine ⟨(2 * Real.pi) ^ (2 * g), by positivity, ?_, fun k y hy => ?_⟩
  · rw [abs_of_nonneg (Real.log_nonneg (one_le_pow₀ hπ)), Real.log_pow]
    push_cast
    exact le_rfl
  have hsec := GlobalTheory.FlatTw.Hol.isSec_modelWt_rdU E H Dw l Xo c σ r U hS hσ hU hpq (wtOf Dw 0 (-4)) (even_wtOf _ _)
    (fun τ i j hij hj => by rw [wtOf_fst τ j hj, wtOf_fst τ i (hij.trans_lt hj)]) K (exZ_wtOf (Dw := Dw) ▸ hK) k
  have hb := FrameDegreeData.bOf_mem (U.X k) hy
  have hz := OrthogonalFrameDomain.rmul_mem_dom (U.X k) hy hb
  have ho := FrameDegreeData.ortho_bOf (U.X k) hy
  have hp := FrameDegreeData.pnorm_rmul (U.X k) _ _ hsec.2.1 y hy _ hb
  generalize rmul y (FrameDegreeData.bOf (U.X k) y) = z at hz ho hp
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h0 : 0 < x := hx k τ₀ ▸ norm_pos_iff.2 ((map_ne_zero τ₀).2 (U.X k).ξ0_ne)
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : FibKey Xo ℂ (U.un k ⟨z, hz⟩).x, Tied (S := ℂ) e (U.un k ⟨z, hz⟩).s (U.un k ⟨z, hz⟩).u Φ :=
    @GlobalTheory.KeyFourth.exists_tied E _ _ _ H Dw l Xo c g e ℂ _ _ σ.toAlgebra (U.un k ⟨z, hz⟩) hpq
  have hv : rdU U (K : Rul Xo c) k z = (κ ℂ Φ.key : ℂ) := by
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, hz, dif_pos]
    exact @hval ℂ _ _ σ.toAlgebra (U.un k ⟨z, hz⟩) Φ hΦ
  have hn : (U.X k).pnorm (modelWt U (wtOf Dw 0 (-4)) k) (rdU U (K : Rul Xo c) k) z = ‖(κ ℂ Φ.key : ℂ)‖ := by
    simp [Data.pnorm, ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho _ ho, hv]
  show lieFacZ Dw x _ * (U.X k).pnorm (modelWt U (wtOf Dw 0 (-4)) k) (rdU U (K : Rul Xo c) k) y = _
  rw [← hp, hn, norm_rule_of_isOrtho hκ e h0 hσ hU k ⟨z, hz⟩ (hx k) ho Φ hΦ, mul_left_comm, lieFacZ_mul e h0, mul_one]

end GlobalTheory.KeyArchNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaOneMapBaseTupleOfCharacterisationExtremal
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapTies

theorem oneMapRow0_of_ties_core : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → IoExt R → ∀ (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), OMPins T R κ v₀ O i → OneMapRow0 T R κ v₀ O i := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ hR ht hio O i hpins
  have h := _root_.GlobalTheory.AdTh.exists_ccIs_equivAt_serOf_oneMapRow_core hCI D G Pl0 T0 A T R F κ v₀ hR ht hio i Unit (fun _ => A.μ0) (O i) hpins.2
  obtain ⟨cc, -, u, -, hequiv, hser, hid⟩ := h
  exact GlobalTheory.OneMapBase.oneMapRow0_of_rows T R κ v₀ O i (u • cc) 1 hpins hequiv hid
    (GlobalTheory.PhRatCommon.phRat_of_ser_core D G Pl0 T0 A T R F κ v₀ hR ht O i hpins (u • cc) hser
      (_root_.GlobalTheory.ClassSumRule.exists_cusp_isThClsD_core hCI D G Pl0 T0 A T R F κ v₀ hR ht i _ _ (O i) hpins.2 ()) hequiv)

end GlobalTheory.OneMapTies
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaOneMapIdentityEveryNormalisedFamily
section
set_option autoImplicit false

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapAll

theorem identityRow_of_core : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) , GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → IoExt R → ∀ i, GlobalTheory.OneMapAll.IdentityRow T R κ v₀ i := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ hR ht hio i Tp tup O _ hO
  obtain ⟨cc, -, u, -, -, -, h⟩ := _root_.GlobalTheory.AdTh.exists_ccIs_equivAt_serOf_oneMapRow_core hCI D G Pl0 T0 A T R F κ v₀ hR ht hio i Tp tup O hO
  exact ⟨u • cc, 1, h⟩

end GlobalTheory.OneMapAll
end

