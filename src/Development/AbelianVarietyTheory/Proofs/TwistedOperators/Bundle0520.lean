module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsLatticeVacuumIffSignedRationalFixed
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0515
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousReprSymm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0509
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1313
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletedDiagonalCoordinateMemCompletionConjAA
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0354
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointFrameRowReductionEqZeroIffMem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LiftDat.RowKer

open GlobalTheory.LiftLevel

variable {D : D7}

theorem row_mat {S T : HSp D} (hS : S.gram = 1) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (a e : AE D) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    adjA S T βS βT a (partAt (cA D e) (finW S T y)) = Matrix.of fun i j => rowAdj T βT a e (y i) 0 j := by
  have hb : βS.val * (βS⁻¹).val = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hg : (S.gram⁻¹).map (incA D) = 1 := by rw [hS, inv_one, Matrix.map_one _ (map_zero _) (map_one _)]
  unfold adjA frMapAdj rowAdj
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hb, Matrix.one_mul, hg, Matrix.one_mul]
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply,
    partAt, finW, smul_eq_mul, Fin.sum_univ_one, map_sum]

theorem rowRed_zero (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (a e : AE D) (PP : Formalism.L2.DIV.Pl D.host.E) :
    rowRed T βT a e PP 0 = 0 := by
  funext j
  have h0 : rowAdj T βT a e 0 = 0 := by
    unfold rowAdj; ext i k; simp [Matrix.mul_apply, Matrix.smul_apply]
  have h1 : ∀ h, Formalism.L2.DIV.resS D.host.F PP (⟨0, h⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = 0 :=
    fun _ => map_zero _
  simp [rowRed, redM, h0, h1]

theorem full_std (n : ℕ) : (stdL D.host.E n).FG ∧
    Submodule.span D.host.E (stdL D.host.E n : Set (Fin n → D.host.E)) = ⊤ := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin n)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span ⟨a, by simp⟩

theorem full_smul {r : ℕ} (I : Ideal (𝓞 D.host.E)) (hI : I ≠ ⊥) (L : Lt D.host.E r) (hL : L.FG)
    (hLs : Submodule.span D.host.E (L : Set (Fin r → D.host.E)) = ⊤) :
    (I • L).FG ∧ Submodule.span D.host.E ((I • L : Lt D.host.E r) : Set (Fin r → D.host.E)) = ⊤ := by
  refine ⟨hL.smul (IsNoetherian.noetherian I), ?_⟩
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have htE : (t : D.host.E) ≠ 0 := fun h => ht0 (RingOfIntegers.ext (h.trans rfl))
  rw [eq_top_iff, ← hLs, Submodule.span_le]
  intro u hu
  have hu' : (t : D.host.E) • u ∈ Submodule.span D.host.E ((I • L : Lt D.host.E r) : Set (Fin r → D.host.E)) :=
    Submodule.subset_span (Submodule.smul_mem_smul ht hu)
  have := Submodule.smul_mem _ ((t : D.host.E)⁻¹) hu'
  rwa [smul_smul, inv_mul_cancel₀ htE, one_smul] at this

end GlobalTheory.LiftDat.RowKer

namespace GlobalTheory.LiftDat.RowKer

open GlobalTheory.LiftLevel

theorem rowRed_eq_zero_iff : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) → ∀ v ∈ C.X.Λ, ((∀ PP ∈ Pg ∪ Q, GlobalTheory.LiftDat.rowRed T βT a e PP v = 0) ↔ v ∈ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ) := by
  intro D S T C hn ΛT _ _ βS βT _ _ Pg Q ξ _ _ e he a k₀ _ _ hgen h1 h2 h3 _ v hv
  rcases Nat.eq_zero_or_pos T.rank with h0 | hpos
  · haveI : IsEmpty (Fin T.rank) := by rw [h0]; infer_instance
    have hv0 : v = 0 := funext fun j => isEmptyElim j
    constructor
    · intro _; rw [hv0]; exact zero_mem _
    · intro _ PP _; funext j; exact isEmptyElim j
  let i0 : Fin S.rank := ⟨0, lt_of_lt_of_le hpos hn⟩
  let y : Matrix (Fin S.rank) (Fin T.rank) D.host.E := Matrix.of fun i => if i = i0 then v else 0
  have hyrow : ∀ i, y i = if i = i0 then v else 0 := fun i => rfl
  have hy0 : y i0 = v := by rw [hyrow, if_pos rfl]
  have hy : ∀ L : Lt D.host.E T.rank, v ∈ L → y ∈ tens (stdL D.host.E S.rank) L := fun L hvL =>
    (GlobalTheory.SW.TensLat.mem_tens_stdL L y).2 fun k => by
      rw [hyrow]
      split_ifs
      · exact hvL
      · exact zero_mem _
  have hAo : ∀ L : Lt D.host.E T.rank, ∀ o : 𝓞 D.host.E, ∀ z ∈ tens (stdL D.host.E S.rank) L,
      (o : D.host.E) • z ∈ tens (stdL D.host.E S.rank) L :=
    fun L o z hz => smul_mem_tens o (fun u hu => Submodule.smul_mem _ o hu) hz
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hce : finPart D (cA D e) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by
      rw [← map_mul, ← map_mul, hee])
  have hfinW : ∀ (L : Lt D.host.E T.rank) (z : Matrix (Fin S.rank) (Fin T.rank) D.host.E),
      z ∈ tens (stdL D.host.E S.rank) L → finW S T z ∈ hatA S T (tens (stdL D.host.E S.rank) L) := fun L z hz => by
    rw [GlobalTheory.Ker.SignVac.finW_eq]; exact GlobalTheory.Ker.SignVac.finTens_mem (GlobalTheory.LatVac.one_mem_intAf _) hz
  have hxL : ∀ L : Lt D.host.E T.rank, v ∈ L →
      partAt (cA D e) (finW S T y) ∈ hatA S T (tens (stdL D.host.E S.rank) L) := fun L hvL => by
    have : partAt (cA D e) (finW S T y) = cA D e • finW S T y := by ext i j; rfl
    rw [this]; exact smul_mem_hatA_of_int (hAo L) hce (hfinW L y (hy L hvL))
  have hhalf : IsHalf (cA D e) (partAt (cA D e) (finW S T y)) := fun i j => by
    simp only [partAt, Matrix.map_apply, ← mul_assoc, ← map_mul, hee]
  obtain ⟨hc1, hc2⟩ := hgen _ hhalf
  have hred : ∀ PP, redM PP (adjA S T βS βT a (partAt (cA D e) (finW S T y))) =
      fun i j => rowRed T βT a e PP (y i) j := by
    intro PP; rw [row_mat C.m.gS βS βT a e y]; rfl
  constructor
  · intro hR
    have hint := hc1.2 (hxL _ hv)
    have hall : ∀ PP ∈ Pg ∪ Q, redM PP (adjA S T βS βT a (partAt (cA D e) (finW S T y))) = 0 := by
      intro PP hPP
      rw [hred]
      funext i j
      rw [hyrow]
      split_ifs
      · exact congrFun (hR PP hPP) j
      · exact congrFun (rowRed_zero T βT a e PP) j
    have hxI := hc2.1 ⟨hint, hall⟩

    have hm : liftI Pg Q ⊔ conjI (liftI Pg Q) = ⊤ := Ideal.isCoprime_iff_sup_eq.1 h3
    have h1' : (1 : 𝓞 D.host.E) ∈ liftI Pg Q ⊔ conjI (liftI Pg Q) := by rw [hm]; exact Submodule.mem_top
    obtain ⟨t, ht, c, hc, htc⟩ := Submodule.mem_sup.1 h1'
    have hcP : ∀ PP ∈ Pg ∪ Q, conjI (liftI Pg Q) ≤ PP.asIdeal := by
      intro PP hPP x hx
      have h2' := mem_of_mem_conjI hx
      rw [liftI] at h2'
      have h3' : stO x ∈ conjI PP.asIdeal := Finset.inf_le (f := fun PP : Formalism.L2.DIV.Pl D.host.E => conjI PP.asIdeal)
        hPP (Ideal.prod_le_inf h2')
      have h4' := mem_of_mem_conjI h3'
      have h5' : stO (stO x) = x := RingOfIntegers.ext (star_star _)
      rwa [h5'] at h4'
    have htP : ∀ PP ∈ Pg ∪ Q, t ∉ PP.asIdeal := by
      intro PP hPP htm
      have h6 : (1 : 𝓞 D.host.E) ∈ PP.asIdeal := htc ▸ add_mem htm (hcP PP hPP hc)
      exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h6)
    have hPQ : (Pg ∪ Q).Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      apply h1
      rw [liftI, hne, Finset.prod_empty, Ideal.one_eq_top]
    have ht0 : (t : D.host.E) ≠ 0 := by
      obtain ⟨PP, hPP⟩ := hPQ
      intro h
      apply htP PP hPP
      have : t = 0 := RingOfIntegers.ext (h.trans rfl)
      rw [this]; exact zero_mem _
    have htL : ∀ u ∈ C.X.Λ, t • u ∈ liftI Pg Q • C.X.Λ := fun u hu => Submodule.smul_mem_smul ht hu
    have hty : (t : D.host.E) • y ∈ tens (stdL D.host.E S.rank) (liftI Pg Q • C.X.Λ) := smul_mem_tens t htL (hy _ hv)
    have hz1 : finPart D (e * incA D ((t : D.host.E))⁻¹) ∈ intAE D :=
      GlobalTheory.IdemSumInt.finPart_idemSum_mul_inv_mem D e (Pg ∪ Q) he t htP
    have e1 : partAt e (finW S T y) = (e * incA D ((t : D.host.E))⁻¹) • finW S T ((t : D.host.E) • y) := by
      have e2 : finW S T ((t : D.host.E) • y) =
          (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (t : D.host.E) : AE D) • finW S T y := by
        rw [GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.LatVac.tmul_smul_finTens, one_mul,
          Matrix.transpose_smul]
      have e3 : finW S T y = (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) • finW S T y := by
        rw [GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.LatVac.tmul_smul_finTens, one_mul, one_smul]
      rw [e2, smul_smul, mul_assoc]
      have e4 : incA D ((t : D.host.E))⁻¹ * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (t : D.host.E) : AE D) =
          pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) := by
        change ((1 : AF D.host.F) ⊗ₜ[D.host.F] ((t : D.host.E))⁻¹) * _ = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ ht0]
      rw [e4, mul_smul, ← e3]
      ext i j; rfl
    have hpe : partAt e (finW S T y) ∈ hatA S T (tens (stdL D.host.E S.rank) (liftI Pg Q • C.X.Λ)) := by
      rw [e1]; exact smul_mem_hatA_of_int (hAo _) hz1 (hfinW _ _ hty)

    have hpo := _root_.GlobalTheory.LiftLevel.OffTens.partAt_finW_off_mem_hatA D S T Pg Q e he C.X.Λ y (hy _ hv)
    have hsum : finW S T y = partAt (cA D e) (finW S T y) + partAt e (finW S T y) +
        partAt (1 - e - cA D e) (finW S T y) := by
      ext i j; simp only [partAt, Matrix.add_apply, Matrix.map_apply]; ring
    have hfI : finW S T y ∈ hatA S T (tens (stdL D.host.E S.rank) (liftI Pg Q • C.X.Λ)) := by
      rw [hsum]; exact add_mem (add_mem hxI hpe) hpo
    have hyI := ((GlobalTheory.Ker.HatLat.hatA_tens D S T C (stdL D.host.E S.rank) (liftI Pg Q • C.X.Λ) (full_std _)
      (full_smul _ h2 C.X.Λ C.X.Λ_fg C.X.Λ_span)).2.1 y).1 hfI
    have := (GlobalTheory.SW.TensLat.mem_tens_stdL _ y).1 hyI i0
    rwa [hy0] at this
  · intro hvI PP hPP
    have h6 := (hc2.2 (hxL _ hvI)).2 PP hPP
    rw [hred] at h6
    funext j
    have h7 := congrFun (congrFun h6 i0) j
    rw [hy0] at h7
    exact h7

end GlobalTheory.LiftDat.RowKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassConditionsCoreFromMixedCoordinateFunction
section
namespace I195MixedCoordinates_8ff71cc19fc82be2cd949563

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_8ff71cc19fc82be2cd949563

public noncomputable abbrev _root_.I195MixedCoordinates_5fec64f1e39721af271f64cb.source :=
  @_root_.I195MixedCoordinates_8ff71cc19fc82be2cd949563.source

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.ClsCoreFromMix

theorem heisO_smul_loc {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (w : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (c • f) = c • heisO ψ S T w f := by
  funext v
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem mixS_smul_loc {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (c : ℂ) (f : WO S T → ℂ) (x : Mx D T.rank ρ) :
    (_root_.I195MixedCoordinates_8ff71cc19fc82be2cd949563.source d) T ψ μ 𝓕 (c • f) x = c • (_root_.I195MixedCoordinates_8ff71cc19fc82be2cd949563.source d) T ψ μ 𝓕 f x := by
  funext w
  simp only [_root_.I195MixedCoordinates_8ff71cc19fc82be2cd949563.source, heisO_smul_loc, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]

theorem isThetaFunO_smul_loc {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {Φ : WO S T → ℂ}
    (hΦ : IsThetaFunO ψ S T Φ) (c : ℂ) : IsThetaFunO ψ S T (c • Φ) := by
  refine ⟨fun γ w => ?_, ?_, continuous_const.mul hΦ.cont, fun k L hL hf w => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, hΦ.quasi γ w]; ring
  · obtain ⟨U, hU, h⟩ := hΦ.level
    refine ⟨U, hU, fun u hu hu' => ?_⟩
    funext w
    have := congrFun (h u hu hu') w
    simp only [heisO, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [← this]; ring
  · exact contDiff_const.mul (hΦ.smooth k L hL hf w)

theorem isHalf_mul {D : D7} {m n k : ℕ} {e : AE D} {u : Mx D m n} (h : IsHalf e u) (M : Mx D n k) :
    IsHalf e (u * M) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, h i]

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (p : Pieces V₀ W W₀ ρ σ) (y : Mx D V₀.rank σ) (β₁ : Mx D W.rank ρ → ℂ) (g' : WO V₀ W → ℂ) (Φ : WO V W → ℂ), IsThetaFunO ψ V₀ W g' → IsThetaFunO ψ V W Φ → (∀ x', (_root_.I195MixedCoordinates_8ff71cc19fc82be2cd949563.source dV) W ψ vS.μ vS.𝓕 Φ x' = β₁ x' • g') → (∀ ξ ∈ p.B₁, heisO ψ V₀ W (dW.incX V₀ ξ) g' = ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) • g') → (∀ η ∈ p.B₂, heisO ψ V₀ W (dW.incY V₀ η) g' = g') → IsLatVac (heisO ψ V₀ W) (p.Γ₀.map (dW.inc0 V₀)) g' → (∀ ξ ∈ p.B₁, heisO ψ V W (dV.ext0 W (dW.incX V₀ ξ)) Φ = ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) • Φ) ∧ (∀ η ∈ p.B₂, heisO ψ V W (dV.ext0 W (dW.incY V₀ η)) Φ = Φ) ∧ IsLatVac (fun w f => heisO ψ V W w f) (p.Γ₀.map ((dV.ext0 W).comp (dW.inc0 V₀))) Φ := by
  intro D ψ hψ V V₀ W W₀ ρ σ dV dW vS p y β₁ g' Φ hg hΦ hmix hB1 hB2 hvac
  have hH := GlobalTheory.HeisMixSource.heis_mixS D ψ hψ V V₀ W ρ dV vS Φ hΦ
  have key : ∀ (w : WO V₀ W) (c : ℂ), heisO ψ V₀ W w g' = c • g' →
      heisO ψ V W (dV.ext0 W w) Φ = c • Φ := by
    intro w c hw
    have hth1 := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hΦ (dV.ext0 W w)
    have hth2 : IsThetaFunO ψ V W (c • Φ) := isThetaFunO_smul_loc hΦ c
    refine (_root_.GlobalTheory.ThetaMixInj.main D ψ hψ V W _ _ hth1 hth2).1 V₀ ρ dV vS (fun x => ?_)
    change (_root_.I195MixedCoordinates_8ff71cc19fc82be2cd949563.source dV) W ψ vS.μ vS.𝓕 (heisO ψ V W (dV.ext0 W w) Φ) x =
      (_root_.I195MixedCoordinates_8ff71cc19fc82be2cd949563.source dV) W ψ vS.μ vS.𝓕 (c • Φ) x
    have hh := hH.2.2.1 x w
    change (_root_.I195MixedCoordinates_8ff71cc19fc82be2cd949563.source dV) W ψ vS.μ vS.𝓕 (heisO ψ V W (dV.ext0 W w) Φ) x =
      heisO ψ V₀ W w ((_root_.I195MixedCoordinates_8ff71cc19fc82be2cd949563.source dV) W ψ vS.μ vS.𝓕 Φ x) at hh
    rw [hh, hmix x, heisO_smul_loc, hw, mixS_smul_loc, hmix x, smul_comm]
  refine ⟨fun ξ hξ => key _ _ (hB1 ξ hξ), fun η hη => by rw [key _ 1 (by rw [one_smul]; exact hB2 η hη), one_smul], ?_, ?_⟩
  · intro u hu
    obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.1 hu
    have h2 : (2 • (((dV.ext0 W).comp (dW.inc0 V₀)) w)) = dV.ext0 W (2 • dW.inc0 V₀ w) := by
      simp only [AddMonoidHom.comp_apply, map_nsmul]
    show heisO ψ V W _ Φ = Φ
    rw [h2, key _ 1 (by rw [one_smul]; exact hvac.1 _ (AddSubgroup.mem_map_of_mem _ hw)), one_smul]
  · intro e he u hu hh
    obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.1 hu
    have hh' : IsHalf e (dW.inc0 V₀ w) := by
      have := isHalf_mul hh dV.j0
      simpa only [AddMonoidHom.comp_apply, HypDec.matrixExtendByZero_apply, Matrix.mul_assoc, HypDec.p0_j0, Matrix.mul_one] using this
    show heisO ψ V W _ Φ = Φ
    rw [AddMonoidHom.comp_apply, key _ 1 (by rw [one_smul]; exact hvac.2 e he _ (AddSubgroup.mem_map_of_mem _ hw) hh'),
      one_smul]

end GlobalTheory.ClsCoreFromMix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassConditionsIsotropicHomFromFirstMixedCoordin
section
namespace I195MixedCoordinates_acb50ed7a993b068b784d65f

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_acb50ed7a993b068b784d65f

public noncomputable abbrev _root_.I195MixedCoordinates_684fc6d6042eff6a430ef673.source :=
  @_root_.I195MixedCoordinates_acb50ed7a993b068b784d65f.source

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem GlobalTheory.ClassFromMixed.main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ), p.Is dV dW x ψ → ∀ (β₁ : Mx D W.rank ρ → ℂ) (g' : WO V₀ W → ℂ) (Φ : WO V W → ℂ), IsThetaFunO ψ V W Φ → (∀ x', (_root_.I195MixedCoordinates_acb50ed7a993b068b784d65f.source dV) W ψ vS.μ vS.𝓕 Φ x' = β₁ x' • g') → (∀ a ∈ p.A₁, ∀ z, β₁ (z + a) = β₁ z) → (∀ z, β₁ z ≠ 0 → ∃ r : Mx D W.rank ρ, r.map (finPart D) = 0 ∧ z - (x + r) ∈ p.A₁) → (∀ a ∈ p.A₁, heisO ψ V W (dV.extX W a) Φ = Φ) ∧ ∀ a ∈ p.A₂, heisO ψ V W (dV.extY W a) Φ = ψ (symplO V W (dV.extX W x) (dV.extY W a)) • Φ := by
  intro D ψ hψ V V₀ W W₀ ρ σ dV dW vS p x hp β₁ g' Φ hΦ hmix hper hsupp
  obtain ⟨hX, hY, -⟩ := GlobalTheory.HeisMixSource.heis_mixS D ψ hψ V V₀ W ρ dV vS Φ hΦ
  change ∀ x', I195MixedCoordinates_5a743adb4eaabe3d936622f8.source dV W ψ vS.μ vS.𝓕 Φ x' = β₁ x' • g' at hmix
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · refine (_root_.GlobalTheory.ThetaMixInj.main D ψ hψ V W _ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hΦ _) hΦ).1 V₀ ρ dV vS
      fun x' => ?_
    change I195MixedCoordinates_5a743adb4eaabe3d936622f8.source dV W ψ vS.μ vS.𝓕 (heisO ψ V W (dV.extX W a) Φ) x' = I195MixedCoordinates_5a743adb4eaabe3d936622f8.source dV W ψ vS.μ vS.𝓕 Φ x'
    rw [hX, hmix, hmix, hper a ha]
  · refine (_root_.GlobalTheory.ThetaMixInj.main D ψ hψ V W _ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hΦ _)
      (GlobalTheory.WeilVacMove.isTheta_smul _ hΦ)).1 V₀ ρ dV vS fun x' => ?_
    change I195MixedCoordinates_5a743adb4eaabe3d936622f8.source dV W ψ vS.μ vS.𝓕 (heisO ψ V W (dV.extY W a) Φ) x' = I195MixedCoordinates_5a743adb4eaabe3d936622f8.source dV W ψ vS.μ vS.𝓕 (ψ (symplO V W (dV.extX W x) (dV.extY W a)) • Φ) x'
    have hsmul := GlobalTheory.HandHom.mixS_smul dV W ψ vS.μ vS.𝓕 (ψ (symplO V W (dV.extX W x) (dV.extY W a))) Φ x'
    change I195MixedCoordinates_5a743adb4eaabe3d936622f8.source dV W ψ vS.μ vS.𝓕 (ψ (symplO V W (dV.extX W x) (dV.extY W a)) • Φ) x' = ψ (symplO V W (dV.extX W x) (dV.extY W a)) • I195MixedCoordinates_5a743adb4eaabe3d936622f8.source dV W ψ vS.μ vS.𝓕 Φ x' at hsmul
    rw [hY, hsmul, hmix]
    by_cases hb : β₁ x' = 0
    · rw [hb, zero_smul, smul_zero, smul_zero]
    · obtain ⟨r, hr, hx'⟩ := hsupp x' hb
      have hfinA : MxAt (fun _ => True) a := hp.a₂.fin a ha
      have hYa : (dV.extY W a).map (infPart D) = 0 := by
        rw [HypDec.extY_apply, Matrix.map_mul]
        have : a.map (infPart D) = 0 := Matrix.ext fun i j => GlobalTheory.FinPlLoc.infPart_of_idAt (hfinA i j)
        rw [this, Matrix.zero_mul]
      have hXr : (dV.extX W r).map (finPart D) = 0 := by
        rw [HypDec.extX_apply, Matrix.map_mul, hr, Matrix.zero_mul]
      have h1 : ψ (symplO V W (dV.extX W (x' - (x + r))) (dV.extY W a)) = 1 :=
        (hp.dualA _ (hp.a₁.fin _ hx')).1 hx' a ha
      have hsplit : x' = x + r + (x' - (x + r)) := by abel
      have key : ψ (symplO V W (dV.extX W x') (dV.extY W a)) = ψ (symplO V W (dV.extX W x) (dV.extY W a)) := by
        rw [hsplit, map_add (f := _), map_add (f := _), GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_left,
          GlobalTheory.SplitScalar.symplO_real_fin V W hXr hYa, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, h1,
          AddChar.map_zero_eq_one, mul_one, mul_one]
      rw [key]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryMovesHeisenbergDerivativeStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactUnitary_moves_heisenbergDerivative : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ X B.emb, ∀ u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u →
    ∀ f f₁ fk h : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) f f₁ → Acts (evI F) (om (k, 1)) f fk →
      Acts (evI F) (om (k, 1)) f₁ h → ActsD (evI F) (M.heisLine B.ψ (mat k * u)) fk h := by
  first | exact @GlobalTheory.KHeisComm.actsD_heisLine_mat_mul | exact GlobalTheory.KHeisComm.actsD_heisLine_mat_mul | (intros; apply GlobalTheory.KHeisComm.actsD_heisLine_mat_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletedDiagonalCoordinateMemCompletionConjAAStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.XCharBF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completed_diagonal_coordinate_mem_completion_conj_AA : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {F : Frames G}, Std F → ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (x : WO (negSp (G.V (.grid (2 * ρ + 2) 0))) (G.V (.grid (2 * ρ + 1) 0))), x ∈ hatMx (G.modul • homLat (G.Λ (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 1) 0))) → ∀ p : Fin ρ, ((F.dJ ρ h).pY ⬝ x ⬝ (F.dB ρ h).jY) p p ∈ complId D.host.AAbar := by
  first | exact @GlobalTheory.XCharBF.HatCoord.hatMx_coord_mem | exact GlobalTheory.XCharBF.HatCoord.hatMx_coord_mem | (intros; apply GlobalTheory.XCharBF.HatCoord.hatMx_coord_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjCharacterEqProdSymmetricEdgeCharacters
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

theorem GlobalTheory.SeeConjChar.conjCharacter_eq_prod_symmetricEdge_characters : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → (∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP)) → ∃ (ψ' : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (a : ∀ PP : Pl D.host.E, Fin D.R.r → Fin D.R.r → (kP PP)ˣ), IsGenericPsi R.Pg ψ' ∧ ∀ κ : GA D (Yc D 0), finE (Yc D 0) κ ∈ St β → ((iotaX X h).toMulEquiv κ).2 ∈ X.K2 → star (X.chi2 ((iotaX X h).toMulEquiv κ).2) = ∏ PP ∈ R.Pg, ψ' PP (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then (a PP i j : kP PP) * ((upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) : GL (Fin D.R.r) (kP PP)).val i j) else 0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hIs hGrp β hβ hred
  classical
  obtain ⟨ψ, hψ, hdec⟩ := _root_.GlobalTheory.SeeConjChar.levelCharacter_on_stabilizer_eq_prod_residue_characters R F X h hIs hGrp
  have hc : ∀ PP ∈ R.Pg, ∃ c : (kP PP)ˣ, ∀ t, ψ (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.conjRes PP t) = ψ PP ((c : kP PP) * t) := by
    intro PP hP
    refine _root_.GlobalTheory.Twist.addChar_eq_mulShift_unit_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 PP.isMaximal) (ψ PP)
      ((ψ (GlobalTheory.IdemSupport.cP PP)).compAddMonoidHom (GlobalTheory.SeeConjChar.conjRes PP).toAddMonoidHom) (hψ PP hP).1 ?_
    intro h1
    apply (hψ PP hP).2
    ext t
    obtain ⟨s, rfl⟩ := (GlobalTheory.SeeConjChar.conjRes PP).surjective t
    have := congrArg (fun χ : AddChar (kP PP) ℂ => χ s) h1
    simpa using this
  choose! c hc using hc
  refine ⟨fun PP => (ψ PP).mulShift (-1), fun PP i j =>
    if (i.1 < D.R.rS ∨ (i.1 + 1 < D.R.rS + D.R.k ∧ GlobalTheory.SeeConjChar.sideAt X h PP = true)) then 1
    else if i.1 = D.R.rS + D.R.k then c PP else -c PP, ?_, ?_⟩
  · intro PP hP h1
    apply (hψ PP hP).1
    ext t
    have := congrArg (fun χ : AddChar (kP PP) ℂ => χ (-t)) h1
    simpa [AddChar.mulShift_apply] using this
  · intro κ hS hK2
    have hK : ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset := (Formalism.L2.SG.Closed.level_subgroup_properties X).2.1 _ hK2
    rw [hdec κ hK, ← starRingEnd_apply, map_prod]
    refine Finset.prod_congr rfl fun PP hP => ?_
    rw [GlobalTheory.T.residue_levelCharacterArgument_at_typePlace R F X h hIs hGrp β hβ hred PP hP κ hS, GlobalTheory.T.residue_conjugatePlace_characterArgument_signedSum R F X h hIs hGrp β hβ hred PP hP κ hS hK2, hc PP hP,
      map_mul, ← AddChar.map_neg_eq_conj, ← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, AddChar.mulShift_apply]
    congr 1
    rw [Finset.mul_sum, ← neg_add, ← Finset.sum_add_distrib, neg_one_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hE
    · unfold GlobalTheory.SeeConjChar.wA GlobalTheory.SeeConjChar.wB
      simp only [apply_ite (fun u : (kP PP)ˣ => (u : kP PP)), Units.val_one, Units.val_neg]
      split_ifs <;> first | (exfalso; tauto) | (push_cast; ring1) | omega | (simp_all <;> omega)
    · simp
end

