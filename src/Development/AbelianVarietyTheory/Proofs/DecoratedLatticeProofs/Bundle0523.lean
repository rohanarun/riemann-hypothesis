module

public import Mathlib
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IncAMulMemIntAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0323
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0582
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0155

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIffFrame
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.LevelData

open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge GlobalTheory.LocMod
open _root_.Formalism.L2.Col (IntAt redP qOf)

section Gen

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {u : D.what₂.Word}

end Gen

section Chain

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_lt_one_iff {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {ι : E →+* k}
    (hi : ∀ x, ι x ∈ 𝒪[k] ↔ IntAt P x) (a : E) : valuation k (ι a) < 1 ↔ P.valuation E a < 1 := by
  by_cases ha : a = 0
  · simp [ha]
  have h := hi a⁻¹
  rw [GlobalTheory.AtTypeExists.intAt_iff, Valuation.mem_integer_iff, map_inv₀, map_inv₀, map_inv₀,
    inv_le_one₀ (zero_lt_iff.2 (by simpa using ha)), inv_le_one₀ (zero_lt_iff.2 (by simpa using ha))] at h
  rw [← not_le, ← not_le, h]

theorem exists_unif {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {ι : E →+* k}
    (hi : ∀ x, ι x ∈ 𝒪[k] ↔ IntAt P x) (hd : DenseRange ι) (h : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) :
    ∃ ϖ : kˣ, (ϖ : k) = ι (qOf P : E) ∧ GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ := by
  have hq := GlobalTheory.AtTypeExists.valuation_norm P h
  have h0 : ((qOf P : ℕ) : E) ≠ 0 := fun e => by
    rw [e, map_zero] at hq
    exact WithZero.exp_ne_zero hq.symm
  have h1 : valuation k (ι (qOf P : E)) < 1 := by
    rw [val_lt_one_iff hi, hq, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  refine ⟨Units.mk0 _ ((map_ne_zero ι).2 h0), rfl, fun x => ⟨fun hx => ?_, fun hx => lt_of_le_of_lt hx h1⟩⟩
  by_cases hx0 : x = 0
  · simp [hx0]
  have h2 : {y : k | valuation k (y - x) < valuation k x} ∈ nhds x := by
    rw [IsValuativeTopology.mem_nhds_iff']
    exact ⟨Units.mk0 (valuation k x) (by simpa using hx0), by simp⟩
  obtain ⟨a, ha⟩ := hd.mem_nhds h2
  have h3 : valuation k (ι a) = valuation k x := by simpa using Valuation.map_add_eq_of_lt_right (valuation k) ha
  have h4 : P.valuation E a < 1 := (val_lt_one_iff hi a).1 (h3 ▸ hx)
  have h5 : IntAt P (a / (qOf P : E)) := by
    rw [GlobalTheory.AtTypeExists.intAt_iff, map_div₀, hq, div_le_one₀ WithZero.exp_pos]
    by_cases ha0 : P.valuation E a = 0
    · simp [ha0]
    · rw [← WithZero.exp_log ha0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h4
      rw [← WithZero.exp_log ha0, WithZero.exp_le_exp]
      omega
  have h6 := (hi _).2 h5
  rw [Valuation.mem_integer_iff, map_div₀, map_div₀, div_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 ((map_ne_zero ι).2 h0))), h3] at h6
  exact h6

theorem mul_sec (q : GlobalTheory.FinPl.SplitPt D k) (x : AE D) (y : k) : x * q.sec y = q.sec (q.pr x * y) := by
  have h := q.sec_pr (x * q.sec y)
  have h' := q.sec_pr (q.sec y)
  rw [map_mul, q.pr_sec] at h
  rw [q.pr_sec] at h'
  rw [h, mul_left_comm, ← h']

end Chain

section Place

end Place

section World

variable {B : Base} {X : PreX B.toPre}

theorem type_prime {P : HeightOneSpectrum (𝓞 B.fields.E)} (hP : P ∈ (B.primes X).vGs) :
    ∃ i, qOf P = B.host.g i ∧ (B.host.g i).Prime ∧ ((B.host.g i : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal ∧
      ((B.host.g i : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal ^ 2 ∧ B.host.g i ∉ B.host.small ∧ B.host.g i ≠ B.host.q ∧ B.host.g i ≠ B.host.d ∧
      B.fields.conjO (X.piG i) ∈ P.asIdeal ∧ X.piG i ∉ P.asIdeal ∧ ∀ v, X.piT v - 1 ∈ P.asIdeal := by
  classical
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨i, hi⟩ : ∃ i, P ∈ (B.primes X).vG i := by
    unfold Formalism.L2.Col.Primes.vGs at hP
    rcases Finset.mem_union.1 hP with h | h
    exacts [⟨0, h⟩, ⟨1, h⟩]
  obtain ⟨h1, h2⟩ := GlobalTheory.TypePrimeUnif.typePrime_mem_and_notMem_sq hX hPr i P hi
  have hp : (B.host.g i).Prime := hPr.g_prime i
  have key : ¬ B.host.g i ∣ B.host.QS * B.host.q * B.host.d := fun h => by
    have h3 : B.host.g i ≡ 1 [MOD B.host.g i] := (hPr.g_cong i).of_dvd h
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.modEq_zero_iff_dvd).1 (h3.symm.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl))))
  have hc : B.fields.conjO (X.piG i) ∈ P.asIdeal := by
    unfold Formalism.L2.Col.Primes.vG Formalism.L2.Col.divs at hi
    split_ifs at hi with h
    · exact h.mem_toFinset.1 hi
    · simp at hi
  refine ⟨i, hPr.vG_norm i P hi, hp, h1, h2, B.host.toHostRaw.notMem_small_of_not_dvd key,
    B.host.toHostRaw.ne_q_of_not_dvd key, B.host.toHostRaw.ne_d_of_not_dvd key, hc, fun h => ?_, fun v => ?_⟩
  · obtain ⟨x, y, e⟩ := hPr.piG_cop i
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (e ▸ add_mem (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ hc)))
  · refine Ideal.mem_of_dvd _ (dvd_trans ?_ (hPr.piT_cong v)) h1
    refine Nat.cast_dvd_cast (Dvd.dvd.mul_left (Dvd.dvd.pow ?_ two_ne_zero) _)
    fin_cases i
    exacts [dvd_mul_right _ _, dvd_mul_left _ _]

end World

end GlobalTheory.SeeSaw.LevelData

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PZeroHyperbolicZeroEqOne
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing Filter
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.Inhab

variable {D : D7}

def intGrp (D : D7) (v : Pl D) : AddSubgroup (AE D) where
  carrier := intAt D (· = v)
  add_mem' ha hb := ⟨add_mem ha.1 hb.1, by rw [RingHom.map_add (f := _)]; exact add_mem ha.2 hb.2⟩
  zero_mem' := ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩
  neg_mem' ha := ⟨neg_mem ha.1, by rw [RingHom.map_neg]; exact neg_mem ha.2⟩

theorem mem_intGrp {v : Pl D} {a : AE D} : a ∈ intGrp D v ↔ a ∈ intAt D (· = v) := Iff.rfl

theorem int_mul {v : Pl D} {a b : AE D} (ha : a ∈ intGrp D v) (hb : b ∈ intGrp D v) : a * b ∈ intGrp D v :=
  ⟨Ideal.mul_mem_left _ _ hb.1, by rw [map_mul]; exact GlobalTheory.HostAdeleIso.intAE_mul_mem D ha.2 hb.2⟩

theorem exists_idem (v : Pl D) :
    ∃ ε : AE D, cA D ε = ε ∧ ε ∈ intAt D (· = v) ∧ ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a := by
  have h := GlobalTheory.LatAlmostStd.tmul_mem_intAt (D := D)
    (GlobalTheory.LatAlmostStd.intSupp_single_mul v (α := 1) fun w => by rw [map_one]; exact one_mem _) 1
  rw [mul_one] at h
  refine ⟨algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)), GlobalTheory.IdemSupport.cA_algebraMap _, h,
    fun a => ⟨fun ha => ?_, fun ha => ha ▸ Ideal.mul_mem_right _ _ h.1⟩⟩
  rw [← Algebra.smul_def]
  exact GlobalTheory.LatAlmostStd.smul_eq_of_mem_idAt ha

theorem int_cA {v : Pl D} {a : AE D} (ha : a ∈ intGrp D v) : cA D a ∈ intGrp D v := by
  obtain ⟨ε, hc, -, hid⟩ := exists_idem v
  refine ⟨(hid _).2 ?_, GlobalTheory.IdemSupport.finPart_cA_mem ha.2⟩
  conv_lhs => rw [← hc, ← map_mul, (hid a).1 ha.1]

theorem int_cA_iff {v : Pl D} {a : AE D} : cA D a ∈ intGrp D v ↔ a ∈ intGrp D v :=
  ⟨fun h => by simpa only [Formalism.L2.Theta.cA_cA] using int_cA h, int_cA⟩

theorem mulVec_mem {v : Pl D} {m n : ℕ} {M : Matrix (Fin m) (Fin n) (AE D)} {y : Fin n → AE D} {i : Fin m}
    (h : ∀ j, M i j * y j ∈ intGrp D v) : (M *ᵥ y) i ∈ intGrp D v := by
  simp only [mulVec, dotProduct]
  exact sum_mem fun j _ => h j

def RatInt (v : Pl D) {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) : Prop :=
  ∀ i j, ∀ a ∈ intGrp D v, incA D (M i j) * a ∈ intGrp D v

theorem ae_family {ι : Type} [Finite ι] {x : ι → D.host.E} (hx : x ≠ 0) :
    ∀ᶠ v : Pl D in cofinite, ∀ a, (∀ k, a * incA D (x k) ∈ intGrp D v) ↔ a ∈ intGrp D v := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hx
  filter_upwards [eventually_all.2 fun j => GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D (x j), GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D (x k)⁻¹] with v h1 h2 a
  refine ⟨fun h => ?_, fun h j => by rw [mul_comm]; exact h1 j a h⟩
  have := h2 _ (h k)
  rwa [mul_left_comm, ← map_mul, inv_mul_cancel₀ hk, map_one, mul_one] at this

def Std (S : HSp D) (L : Lat S) (v : Pl D) : Prop := ∀ y, y ∈ latV S L (· = v) ↔ ∀ i, y i ∈ intGrp D v

theorem ae_std {S : HSp D} {L : Lat S} (h : IsSelfDualC S L) : ∀ᶠ v : Pl D in cofinite, Std S L v :=
  GlobalTheory.LatAlmostStd.eventually_latV_iff D S L (GlobalTheory.ProjXCols.selfDual_isFullLattice S L h)

theorem ae_latO {S T : HSp D} {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) :
    ∀ᶠ v : Pl D in cofinite, ∀ u : WO S T, u ∈ latO S T (LS : Set _) (LT : Set _) (· = v) ↔ ∀ i j, u i j ∈ intGrp D v := by
  filter_upwards [ae_std hS, ae_std hT, GlobalTheory.FinPl.AlmostAll.latA_eq_latV D] with v h1 h2 h3 u
  obtain ⟨ε, -, hε, hid⟩ := exists_idem v
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT, h3]
  refine ⟨fun ⟨hm, h⟩ i j => ?_, fun h => ⟨fun i j => (h i j).1, fun y hy => (h2 _).2 fun i =>
    mulVec_mem fun j => int_mul (h i j) ((h1 y).1 hy j)⟩⟩
  have := (h2 _).1 (h (Pi.single j ε) ((h1 _).2 fun k => by
    by_cases hk : k = j
    · subst hk; rw [Pi.single_eq_same]; exact hε
    · rw [Pi.single_eq_of_ne hk]; exact zero_mem _)) i
  rw [mulVec_single] at this
  have e : u i j * ε = u i j := by rw [mul_comm]; exact (hid _).1 (hm i j)
  rw [← e]
  exact this

def RatCols {m n : ℕ} (x : Mx D m n) : Prop := ∀ i, ∃ c : Fin m → D.host.E, c ≠ 0 ∧ ∀ k, x k i = incA D (c k)

theorem RatCols.ae {m n : ℕ} {x : Mx D m n} (h : RatCols x) :
    ∀ᶠ v : Pl D in cofinite, ∀ i a, (∀ k, colMul x i a k ∈ intGrp D v) ↔ a ∈ intGrp D v := by
  refine eventually_all.2 fun i => ?_
  obtain ⟨c, hc, e⟩ := h i
  simpa only [colMul, e] using ae_family hc

theorem ratCols_jX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : RatCols d.jX := fun i => by
  refine ⟨fun k => d.e k i, fun h => ?_, fun _ => rfl⟩
  have := congrFun (congrFun d.e'e i) i
  rw [Matrix.mul_apply, one_apply_eq, Finset.sum_eq_zero fun k _ => by rw [show d.e k i = 0 from congrFun h k, mul_zero]] at this
  exact zero_ne_one this

theorem ae_colsAt {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {x : Mx D W.rank ρ} (hx : RatCols x) {LV : Lat V}
    {LW : Lat W} (hV : IsSelfDualC V LV) (hW : IsSelfDualC W LW) : ∀ᶠ v : Pl D in cofinite, ColsAt d x LV LW v := by
  filter_upwards [ae_std hV, ae_std hW, GlobalTheory.FinPl.AlmostAll.latA_eq_latV D, (ratCols_jX d).ae, hx.ae] with v h1 h2 h3 h4 h5 i a _
  rw [h3, h1, h2, h4, h5]

theorem ae_primAt {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    {L : Lat S} (h : IsSelfDualC S L) : ∀ᶠ v : Pl D in cofinite, PrimAt ψ d L v := by
  filter_upwards [ae_std h, (ratCols_jX d).ae, GlobalTheory.FinPl.Conductor.eventually_conductor D ψ hψ] with v h1 h2 h3 i j _ s hs
  obtain ⟨ε, -, hε, hid⟩ := exists_idem v
  simp only [h1 _, h2]
  rw [h3 s hs]
  refine ⟨fun h => ?_, fun h a ha => int_mul h ha⟩
  have := h ε hε
  rwa [mul_comm, (hid s).1 hs] at this

theorem incAdj_smul {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (a : AE D) (y : Mx D S.rank ρ) :
    d.incAdj S (a • y) = cA D a • (show Mx D T.rank S.rank from d.incAdj S y) := by
  show d.jY * (incA D (-D.host.xi0⁻¹) • (adj (a • y) * gA S)) = cA D a • (d.jY * (incA D (-D.host.xi0⁻¹) • (adj y * gA S)))
  rw [adj_smul, Matrix.smul_mul, smul_comm, Matrix.mul_smul]

theorem incAdj_yZero {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) {z : Fin S.rank → D.host.E} (hz : z ≠ 0)
    (hρ : 0 < ρ) : ∃ M : Matrix (Fin T.rank) (Fin S.rank) D.host.E, M ≠ 0 ∧ d.incAdj S (yZero S ρ z) = rat M := by
  let y : Matrix (Fin S.rank) (Fin ρ) D.host.E := of fun k i => if i.1 + 1 = ρ then -z k else 0
  have hy : yZero S ρ z = rat y := by
    ext k i
    show -(incA D (z k) * (if i.1 + 1 = ρ then 1 else 0)) = incA D (if i.1 + 1 = ρ then -z k else 0)
    split_ifs
    · rw [mul_one, RingHom.map_neg]
    · rw [mul_zero, neg_zero, RingHom.map_zero]
  refine ⟨d.e' * (-D.host.xi0⁻¹ • (yᴴ * S.gram)), fun h => hz ?_, ?_⟩
  · have h1 : d.qY * d.e' = 1 := rat_injective (by rw [rat_mul, rat_one]; exact d.pY_jY)
    have h2 : -D.host.xi0⁻¹ • (yᴴ * S.gram) = 0 := by
      rw [← Matrix.one_mul (-D.host.xi0⁻¹ • _), ← h1, Matrix.mul_assoc, h, Matrix.mul_zero]
    rw [smul_eq_zero, neg_eq_zero, inv_eq_zero] at h2
    have h3 : yᴴ = 0 := by
      rw [← Matrix.mul_one yᴴ, ← mul_nonsing_inv _ (gram_isUnit_det S), ← Matrix.mul_assoc,
        h2.resolve_left (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D), Matrix.zero_mul]
    funext k
    have h4 := congrFun (congrFun (conjTranspose_eq_zero.1 h3) k) ⟨ρ - 1, by omega⟩
    simpa [y, show ρ - 1 + 1 = ρ by omega] using h4
  · rw [hy, rat_mul, rat_smul, rat_mul, rat_conjTranspose]
    rfl

section Split

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end Split

section Frames

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {p : SplitPt D k} {n : Type} [Fintype n] [DecidableEq n]

end Frames

section Ram

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Ram

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end GlobalTheory.FinPl.Inhab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralUnramifiedPlacesUnionEqLocalFactors
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.EulStep

theorem isOpen_openOff {D : D7} (A : HSp D) (L : Lat A) (hL : IsSelfDualC A L) (S : Finset (FinPl D)) :
    IsOpen (openOff A L S) := by
  have := GlobalTheory.ProjXCols.selfDual_isFullLattice A L hL
  let U : Subgroup (GA D A) :=
    ⨅ k, ⨅ (_ : k ∉ S), (stabLoc D.sp.cm.sig A.gram L k).comap (proj D.sp.cm.sig A.gram k)
  have hU : ∀ g, g ∈ U ↔ g ∈ openOff A L S := fun g => by simp [U, Subgroup.mem_iInf, openOff]
  have hUo : IsOpen (U : Set (GA D A)) :=
    Subgroup.isOpen_mono (H₁ := ⨅ k, (stabLoc D.sp.cm.sig A.gram L k).comap (proj D.sp.cm.sig A.gram k))
      (fun g hg => (hU g).2 fun k _ => Subgroup.mem_iInf.1 hg k)
      (by
        convert (isRestrGroup_GAd D.sp.cm.sig A.gram L).isOpen_all using 1
        ext g
        simp [Subgroup.mem_iInf])
  convert hUo using 1
  exact Set.ext fun g => (hU g).symm

theorem sphFun_of_param {D : D7} {V : HSp D} {Λ : Lat V} {Sf : Finset (FinPl D)} {f : GA D V → ℂ}
    {B : GlobalTheory.LFun.Fam D.host.E} (hf : GlobalTheory.LFun.IsParamFun D.sp.cm.sig V.gram Λ (Sf : Set (FinPl D)) f B) :
    SphFun V Λ Sf f := by
  intro v hv k hk g
  obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  have hx := (hf v (by simpa using hv) w hw).mem_fixed
  have := congrFun (hx ⟨k, hk⟩) g
  simpa [GlobalTheory.PRep.rightReg, LinearMap.funLeft] using this

theorem setIntegral_openOff_union : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, SphFactor D → LocalZetaOn D (fun _ => True) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → ∀ (LA : Lat A) (LB : Lat B) (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ), IsThetaFunO ψ A B Φ₁ → IsThetaFunO ψ A B Φ₂ → Unram ψ A B χB LA LB Sf Φ₁ Φ₂ → ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, ∀ par : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsParamFun D.sp.cm.sig A.gram LA (Sf : Set (FinPl D)) u₁ par → SphFun A LA Sf u₂ → ∀ s : ℂ, (A.rank : ℝ) < s.re → Integrable (integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s) m → ∀ S₁ S₂ : Finset (FinPl D), Sf ⊆ S₁ → Disjoint S₁ S₂ → ∀ S₃ : Finset (FinPl D), (∀ u, u ∈ S₃ ↔ u ∈ S₁ ∨ u ∈ S₂) → ∫ g in openOff A LA S₃, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m = (∏ v ∈ S₂, GlobalTheory.LFun.LvTw par (GlobalTheory.LFun.val χB) v (s + 1 / 2) / GlobalTheory.LFun.dv D.host.E A.rank B.rank v s) * ∫ g in openOff A LA S₁, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m := by
  intro hP D hSF hLZ ψ θ A B χA χB sA sB t cA a om ν 𝓕 hpair LA LB Sf Φ₁ Φ₂ hΦ₁ hΦ₂ hU m hm u₁ hu₁ u₂ hu₂ par hpar hsph
    s hs hint
  have : BorelSpace (GA D A) := ⟨rfl⟩
  have := GlobalTheory.ProjXCols.selfDual_isFullLattice A LA hU.sdA
  have hsph₁ : SphFun A LA Sf u₁ := sphFun_of_param hpar
  have step : ∀ (S : Finset (FinPl D)) (v : FinPl D), Sf ⊆ S → v ∉ S → ∀ S' : Finset (FinPl D),
      (∀ u, u ∈ S' ↔ u = v ∨ u ∈ S) →
      ∫ g in openOff A LA S', integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m =
        GlobalTheory.LFun.LvTw par (GlobalTheory.LFun.val χB) v (s + 1 / 2) / GlobalTheory.LFun.dv D.host.E A.rank B.rank v s *
          ∫ g in openOff A LA S, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m := by
    intro S v hS hv S' hS'
    have hvf : v ∉ Sf := fun h => hv (hS h)
    rw [_root_.GlobalTheory.Core.Rk.HaarStep.integral_openOff_insert D A LA hU.sdA m hm S v hv (haarLoc D.sp.cm.sig A.gram LA v) inferInstance
      (haarLoc_stabLoc D.sp.cm.sig A.gram LA v) S' hS' _ hint.integrableOn, ← integral_const_mul]
    refine setIntegral_congr_fun (isOpen_openOff A LA hU.sdA S).measurableSet fun x hx => ?_
    obtain ⟨φ, hφ, hfac⟩ := hSF ψ θ A B χA χB sA sB t cA a om ν 𝓕 hpair LA LB Sf Φ₁ Φ₂ hΦ₁ hΦ₂ hU v hvf s
    have hk : proj D.sp.cm.sig A.gram v x ∈ stabLoc D.sp.cm.sig A.gram LA v := hx v hv
    obtain ⟨x', hx'⟩ : ∃ x', x' = x * (emb D.sp.cm.sig A.gram v (proj D.sp.cm.sig A.gram v x))⁻¹ := ⟨_, rfl⟩
    have hx1 : proj D.sp.cm.sig A.gram v x' = 1 := by
      rw [hx', map_mul, map_inv, proj_emb_self, mul_inv_cancel]
    have hxe : x = x' * emb D.sp.cm.sig A.gram v (proj D.sp.cm.sig A.gram v x) := by
      rw [hx', inv_mul_cancel_right]
    have hc := _root_.GlobalTheory.Core.Rk.SphCoef.isSphCoef_rcoef hP D θ A cA LA hpair.setting.2.2.2.1 m hm Sf u₁ hu₁ u₂ hu₂ par hpar hsph v hvf x' hx1
    have hz := (hLZ A LA hU.sdA χB B.rank hpair.weil.hecT hpair.weil.resT v trivial
      (fun w hw => hU.unr w (by
        show ¬ (w.under (𝓞 D.host.F) ∈ (Sf : Set (FinPl D)))
        rw [hw]; simpa using hvf))
      (haarLoc D.sp.cm.sig A.gram LA v) inferInstance (haarLoc_stabLoc D.sp.cm.sig A.gram LA v) s hs φ hφ par _ hc).2
    have hφk : φ (ioAt A v (proj D.sp.cm.sig A.gram v x)) = 1 := by
      have := hφ.2.1 (ioAt A v (proj D.sp.cm.sig A.gram v x))
        ((ioH_mem_KFin (gram_hdbl A)).2 ⟨hk, one_mem _⟩) 1
      rw [one_mul, hφ.2.2] at this
      exact this
    have hr : rcoef m u₁ u₂ x = rcoef m u₁ u₂ x' := by
      have : rTr A x u₁ = rTr A x' u₁ := funext fun g => by
        simp only [rTr]
        conv_lhs => rw [hxe, ← mul_assoc]
        exact hsph₁ v hvf _ hk _
      simp only [rcoef, this]
    have hw := hfac x' hx1 (proj D.sp.cm.sig A.gram v x)
    rw [← hxe, hφk, mul_one] at hw
    simp only [← hx', integrand, hfac x' hx1, hw, hr, mul_assoc]
    rw [integral_const_mul, integral_const_mul, hz, map_one, mul_one]
    ring
  intro S₁ S₂ hS₁
  classical
  induction S₂ using Finset.induction_on with
  | empty =>
    intro _ S₃ h
    obtain rfl : S₃ = S₁ := Finset.ext fun u => by simpa using h u
    simp
  | insert v S₂ hv ih =>
    intro hd S₃ h
    rw [Finset.disjoint_insert_right] at hd
    rw [step (S₁ ∪ S₂) v (hS₁.trans Finset.subset_union_left) (by simp [hd.1, hv]) S₃
      (fun u => by rw [h u, Finset.mem_insert, Finset.mem_union]; tauto),
      ih hd.2 _ (fun u => Finset.mem_union), Finset.prod_insert hv, mul_assoc]

end GlobalTheory.Core.Rk.EulStep

end
end

