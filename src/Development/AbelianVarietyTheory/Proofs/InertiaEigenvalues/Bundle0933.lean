module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0925
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0924
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0616
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0803
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0382
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousNormFin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0926
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StandardFrameNonsplitMaxCompactInLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open scoped TensorProduct

noncomputable section
set_option maxHeartbeats 1000000

namespace GlobalTheory.NonSplitLevel

theorem comp_swapCast {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2) (Q : HeightOneSpectrum (𝓞 E))
    (x y : E ⊗[F2] FiniteAdeleRing (𝓞 F2) F2)
    (e : Algebra.TensorProduct.map (AlgHom.id F2 E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F2 (Q.under (𝓞 F2))) x =
      Algebra.TensorProduct.map (AlgHom.id F2 E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F2 (Q.under (𝓞 F2))) y) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F1 (Q.under (𝓞 F1))) (AlgHom.id F1 E) ((swapCast h).symm x) =
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F1 (Q.under (𝓞 F1))) (AlgHom.id F1 E) ((swapCast h).symm y) := by
  subst h
  have key : ∀ z : E ⊗[F1] FiniteAdeleRing (𝓞 F1) F1,
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F1 (Q.under (𝓞 F1))) (AlgHom.id F1 E) ((swapCast (rfl : F1 = F1)).symm z) =
        Algebra.TensorProduct.comm F1 E _
          (Algebra.TensorProduct.map (AlgHom.id F1 E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F1 (Q.under (𝓞 F1))) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b => rfl
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  rw [key, key, e]

variable {D : D7}

theorem projV_eq_one {V : TH.HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {P : Formalism.IndefR.principalLevelFrame.RowPsi V n}
    (hP : StdFrame hF P) (κ : GAf D.host.E n) (Q : PlE D.host)
    (hκ : (κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map
      (compAt D.host.E (HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) Q)) = 1) :
    GlobalTheory.FinZeta.projV V (Q.under (𝓞 D.host.F)) (P.ψ κ) = 1 := by
  classical
  obtain ⟨⟨β, β', h1, -, hβ⟩, -⟩ := hP
  let g := (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F (Q.under (𝓞 D.host.F))) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hK : ((κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map (swapCast hF).symm).map g = 1 := by
    ext i j
    have e2 := congrFun (congrFun hκ i) j
    rw [Matrix.map_apply] at e2
    rw [Matrix.map_apply, Matrix.map_apply]
    rw [Matrix.one_apply] at e2 ⊢
    split_ifs at e2 ⊢
    · exact (comp_swapCast hF Q _ 1 (e2.trans (map_one _).symm)).trans (by rw [map_one, map_one])
    · exact (comp_swapCast hF Q _ 0 (e2.trans (map_zero _).symm)).trans (by rw [map_zero, map_zero])
  refine GlobalTheory.AdelicU.matHom_injective _ D.sp.cm.sig V.gram (Units.ext ?_)
  rw [MonoidHom.map_one, Units.val_one]
  have e1 : (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.FinZeta.projV V (Q.under (𝓞 D.host.F)) (P.ψ κ))).1 =
      (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (P.ψ κ)).map g :=
    Matrix.ext fun i j => (GlobalTheory.FinZeta.LevelOff.evalV_finPart (Q.under (𝓞 D.host.F)) _).symm
  rw [e1, hβ κ, Matrix.map_mul, Matrix.map_mul, hK, Matrix.mul_one, ← Matrix.map_mul, h1,
    Matrix.map_one _ (map_zero g) (map_one g)]

theorem split_of_not_conj {Q : PlE D.host} (h : ¬ Formalism.IndefR.Lev.IsConjPl Q Q) : IsSplitPl D.host Q := by
  unfold Formalism.IndefR.Lev.IsConjPl at h
  push Not at h
  obtain ⟨c, hc, h⟩ := h
  have e : star (c : D.host.E) = D.host.conj c := by
    apply D.host.φ₀.injective
    have := D.host.isCMField_hostE
    exact (IsCMField.complexEmbedding_complexConj _ D.host.φ₀ _).trans
      (D.host.conjE_apply D.host.φ₀ _).symm
  exact ⟨c, hc, fun y hy hyQ => h y hyQ (hy.trans e.symm)⟩

theorem mem_level {V : TH.HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {P : Formalism.IndefR.principalLevelFrame.RowPsi V n}
    (hP : StdFrame hF P) {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hB : Formalism.IndefR.Lev.IsBaseFrame V β Λ 1) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (hL : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → IsSplitPl D.host PP) {w' : PlE D.host} (hw : ¬ IsSplitPl D.host w')
    {κ : GAf D.host.E n} (hU : κ ∈ Umax D.host.E n)
    (hT : TrivOutside {HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w'} κ) :
    P.ψ κ ∈ Formalism.IndefR.Links.levS V β L ∧ Formalism.IndefR.Lev.levChi V β L (P.ψ κ) = 1 := by
  have hS := (GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hB (P.into κ)).2 ((hP.2 κ).1 hU)
  have hred : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → Formalism.L2.DIV.redFn β PP (Formalism.IndefR.Lev.finE V (P.ψ κ)) = 1 := by
    intro PP hPP
    refine GlobalTheory.FinZeta.LevelOff.redFn_eq_one_of_proj β {(_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)} hS (fun u hu => ?_) (Finset.mem_singleton_self _)
    rw [Finset.mem_singleton.1 hu]
    refine projV_eq_one hP κ PP (hT _ fun e => ?_)
    have e' : HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) PP =
        HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w' := e
    exact GlobalTheory.SphNonSplit.not_split_of_overPl D (w := w') (w' := PP)
      (v := HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w') rfl
      (congrArg HeightOneSpectrum.asIdeal e') hw (hL PP hPP)
  refine ⟨⟨P.into κ, GlobalTheory.LevSplit.mem_lev_of_red _ _ β L _ (GlobalTheory.LevSplit.finE_mem_UA V _) hS hred⟩, ?_⟩
  unfold Formalism.IndefR.Lev.levChi
  rw [GlobalTheory.LevSplit.levFn_eq_one β L _ hred, Units.val_one]

theorem lift_level : OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ (i : Fin (w.st Z).toD7.R.m)
      (P : Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (w.st Z).toD7 i) (w.st Z).toD7.R.nV), StdFrame Y.hF P →
      ∀ w' : PlE (w.st Z).toD7.host, ¬ IsSplitPl (w.st Z).toD7.host w' →
      ∀ κ ∈ Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV,
        TrivOutside {HeightOneSpectrum.under (𝓞 (maximalRealSubfield (w.st Z).toD7.host.E)) w'} κ →
        P.ψ κ ∈ Formalism.IndefR.Links.levS _ (z.R.toRealDat.βV i)
            (Formalism.IndefR.RecTie.datVP z.R.toRealDat i (Y.tupT (w.st Z).toD7.what₂.mu0) (z.R.toRealDat.levR z.F.lv2 false)) ∧
          Formalism.IndefR.Lev.levChi _ (z.R.toRealDat.βV i)
            (Formalism.IndefR.RecTie.datVP z.R.toRealDat i (Y.tupT (w.st Z).toD7.what₂.mu0) (z.R.toRealDat.levR z.F.lv2 false))
            (P.ψ κ) = 1 := by
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w _ Z Wt hX z p0 Y _ _ _ _ _ i P hP w' hw κ hU hT => ?_
  have hlev := z.pins.char.base.lev
  obtain ⟨c, hc⟩ := hlev.βV i
  rw [one_pow] at hc
  refine mem_level hP hc _ (fun PP hPP => ?_) hw hU hT
  rcases hPP with h | h
  · obtain ⟨k, hk⟩ := (hlev.Pg PP).1 h
    exact GlobalTheory.SphNonSplit.split_of_over_g _ k (GlobalTheory.Mem.TypePl.div_over _ hk)
  · exact split_of_not_conj ((hlev.Q_pl _ PP h).2 PP h)

end GlobalTheory.NonSplitLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StandardFrameSplitConjMemIntegralMatrices
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
open Formalism.IndefR.principalLevelFrame Formalism.IndefR.Mult

noncomputable section

namespace GlobalTheory.SplitFrameKO

theorem valued_le_one_of_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (c : v.adicCompletion F ≃+* w.adicCompletion E) (hc : Continuous c) (y : v.adicCompletion F)
    (hy : Valued.v y ≤ 1) : Valued.v (c y) ≤ 1 := by
  by_contra hne
  push_neg at hne
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero] at hne
    exact absurd hne (not_lt.2 zero_le')
  have h1 : Valued.v (c y⁻¹) < 1 := by
    rw [map_inv₀, map_inv₀]
    exact inv_lt_one_of_one_lt₀ hne
  have h2 := GlobalTheory.FixedAtSplit.valued_lt_one_of_map c hc _ h1
  rw [map_inv₀] at h2
  have h3 : 1 < Valued.v y := by
    have hpos : 0 < Valued.v y := by
      rw [zero_lt_iff]; exact (map_ne_zero _).2 hy0
    exact (inv_lt_one₀ hpos).1 h2
  exact absurd hy (not_le.2 h3)

theorem val_le_one_of_mem_KO {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    (κ : GL (Fin n) (w.adicCompletion E)) (hκ : κ ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n)) (a b : Fin n) :
    Valued.v ((κ : Matrix (Fin n) (Fin n) (w.adicCompletion E)) a b) ≤ 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  exact he.le_one_iff_le_one.1 ((Valuation.mem_integer_iff _ _).1 (((GlobalTheory.SplitFlip.mem_KO_iff κ).1 hκ).1 a b))

end GlobalTheory.SplitFrameKO

namespace GlobalTheory.SplitFrameKO


set_option maxHeartbeats 2000000 in
theorem main : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)), GlobalTheory.Mem.R3.StdFrame hF P → ∀ (s : SplitPlace D.host.E), ∃ h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield D.host.E)), ∀ κ : Formalism.AUTREP.GAf D.host.E n, TrivOutside {s.v} κ → h⁻¹ * s.loc n κ * h ∈ GlobalTheory.SplitWeil.KO (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin n) → ∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt s.w ((β⁻¹ * finE V (P.ψ κ) * β).val a b)) ≤ 1 := by
  intro D V n hF P β hS s
  obtain ⟨⟨βs, βs', h1, h2, hfr⟩, -⟩ := hS
  obtain ⟨c, hc, hc', hci⟩ := GlobalTheory.SplitComplHomeo.exists_complEquiv D.host.E s
  obtain ⟨f, hf⟩ : ∃ f : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) →+* s.w.adicCompletion D.host.E,
    f = (GlobalTheory.StdFrames.cpt s.w).comp (swapAE D) := ⟨_, rfl⟩
  have hn : V.rank = n := GlobalTheory.SplitFrameW.eq_of_mul_eq_one (βs.map f) (βs'.map f)
    (by rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero f) (map_one f)])
    (by rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero f) (map_one f)])
  subst hn
  obtain ⟨Φc, hΦc⟩ : ∃ Φc : Matrix (Fin V.rank) (Fin V.rank) (EAf D) →+*
      Matrix (Fin V.rank) (Fin V.rank) (s.v.adicCompletion (maximalRealSubfield D.host.E)),
    Φc = (c.symm.toRingHom.comp (GlobalTheory.StdFrames.cpt s.w)).mapMatrix := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin V.rank) (Fin V.rank) (EAf D), B = βs.map (swapAE D) := ⟨_, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ B' : Matrix (Fin V.rank) (Fin V.rank) (EAf D), B' = βs'.map (swapAE D) := ⟨_, rfl⟩
  have hBB : B * B' = 1 := by
    rw [hB, hB', ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBB' : B' * B = 1 := by
    rw [hB, hB', ← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨X, hX⟩ : ∃ X, X = Φc ((β⁻¹).val * B) := ⟨_, rfl⟩
  obtain ⟨X', hX'⟩ : ∃ X', X' = Φc (B' * β.val) := ⟨_, rfl⟩
  have hXX : X * X' = 1 := by
    rw [hX, hX', ← map_mul, show (β⁻¹).val * B * (B' * β.val) = (β⁻¹).val * (B * B') * β.val by
      simp only [Matrix.mul_assoc], hBB, Matrix.mul_one, Units.inv_mul, map_one]
  have hXX' : X' * X = 1 := by
    rw [hX, hX', ← map_mul, show B' * β.val * ((β⁻¹).val * B) = B' * (β.val * (β⁻¹).val) * B by
      simp only [Matrix.mul_assoc], Units.mul_inv, Matrix.mul_one, hBB', map_one]
  obtain ⟨g, hg⟩ : ∃ g : GL (Fin V.rank) (s.v.adicCompletion (maximalRealSubfield D.host.E)),
    g = ⟨X', X, hXX', hXX⟩ := ⟨_, rfl⟩
  refine ⟨g, fun κ _ hk a b => ?_⟩
  have hK : Φc (((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)).map (swapCast hF).symm).map (swapAE D)) =
      ((s.loc V.rank κ : GL _ _) : Matrix _ _ _) := by
    rw [hΦc]
    refine Matrix.ext fun i j => ?_
    change c.symm (((GlobalTheory.StdFrames.toAd D).comp (swapAE D)) ((swapCast hF).symm (κ.1.val i j)) s.w) = s.proj (κ.1.val i j)
    rw [GlobalTheory.SplitFrameW.cpt_swap D.host.F hF ((GlobalTheory.StdFrames.toAd D).comp (swapAE D)) (fun a x => GlobalTheory.StdFrames.toAd_spec D x a) s c hc hci]
    exact c.symm_apply_apply _
  have e1 : (finE V (P.ψ κ)).val = B * (((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)).map
      (swapCast hF).symm).map (swapAE D)) * B' := by
    change (finMat D.sp.cm.sig V.gram (P.ψ κ)).map (swapAE D) = _
    rw [hfr κ, Matrix.map_mul, Matrix.map_mul, hB, hB']
  have hM : Φc ((β⁻¹ * finE V (P.ψ κ) * β).val) = X * ((s.loc V.rank κ : GL _ _) : Matrix _ _ _) * X' := by
    rw [Units.val_mul, Units.val_mul, e1, ← hK, hX, hX', ← map_mul, ← map_mul]
    simp only [Matrix.mul_assoc]
  have e3 : (↑(g⁻¹ * s.loc V.rank κ * g) : Matrix (Fin V.rank) (Fin V.rank) (s.v.adicCompletion (maximalRealSubfield D.host.E))) =
      X * ((s.loc V.rank κ : GL _ _) : Matrix _ _ _) * X' := by
    rw [hg]; rfl
  have hent : Φc ((β⁻¹ * finE V (P.ψ κ) * β).val) a b =
      c.symm (GlobalTheory.StdFrames.cpt s.w ((β⁻¹ * finE V (P.ψ κ) * β).val a b)) := by
    rw [hΦc]; rfl
  have e2 : GlobalTheory.StdFrames.cpt s.w ((β⁻¹ * finE V (P.ψ κ) * β).val a b) =
      c ((↑(g⁻¹ * s.loc V.rank κ * g) : Matrix (Fin V.rank) (Fin V.rank) (s.v.adicCompletion (maximalRealSubfield D.host.E))) a b) := by
    rw [e3, ← hM, hent, c.apply_symm_apply]
  rw [e2]
  exact valued_le_one_of_map c hc _ (val_le_one_of_mem_KO _ hk a b)

end GlobalTheory.SplitFrameKO
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistCharacterUnramifiedInf
section
noncomputable section

namespace GlobalTheory.LiftChar

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

theorem charAt (D : D7) (cf : CharFrame D) (C : CharSide D cf) (j : Fin D.R.m) :
    ∃ μ : D.naut.CG 1, (C.e1 μ).1 = cf.mu0 j ∧ D.naut.csd μ ∧
      (∀ w, ¬ IsSplitPl D.host w → D.naut.unr (D.naut.locG μ w) ∧ D.naut.unr (D.naut.locG D.naut.etaTinv w)) ∧
      ∀ τ, D.naut.infG D.naut.etaTinv (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = {-(1 / 2 : ℂ)} ∧
        D.naut.infG D.naut.etaTinv (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) = {(1 / 2 : ℂ)} := by
  have hm := cf.isMu0 j
  refine ⟨C.e1.symm ⟨cf.mu0 j, hm.unitary⟩, by simp, ?_, ?_, ?_⟩
  · rw [C.csd, Equiv.apply_symm_apply]
    exact GlobalTheory.CsdTriv.isCSD_of_trivOn _ _ _ hm.triv
  · intro w hw
    refine ⟨(C.unr_iff _ w).2 ?_, (C.unr_iff _ w).2 ?_⟩
    · rw [Equiv.apply_symm_apply]
      refine hm.unr w fun k hk => hw ?_
      exact (Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w hk).2.2.1
    · rw [C.etaTinv]
      intro x hx
      have := cf.isEta.unr w x hx
      show ((cf.eta.loc w) x)⁻¹ = 1
      rw [this, inv_one]
  · have hinf : (C.e1 D.naut.etaTinv).1.HasInfQ (embPsi D.host) (fun _ => -(1/2 : ℚ)) := by
      rw [C.etaTinv]
      refine ⟨fun _ => -1, fun _ => by norm_num, fun k => ?_⟩
      have h := cf.isEta.inf k
      show (((cf.eta.inf k)⁻¹ : ℂˣ) : ℂ) = _
      rw [Units.val_inv_eq_inv_val, h]
      simp only [zpow_one, zpow_neg_one, Finset.prod_inv_distrib]
    intro τ
    obtain ⟨h1, h2⟩ := C.infG _ _ hinf (D.eTau τ)
    refine ⟨?_, ?_⟩
    · show D.naut.infG _ (embPsi D.host (D.eTau τ)) = _
      rw [h1]
      congr 1
      push_cast
      ring
    · show D.naut.infG _ ((starRingEnd ℂ).comp (embPsi D.host (D.eTau τ))) = _
      rw [h2]
      congr 1
      push_cast
      ring

end GlobalTheory.LiftChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedWhittakerIntegralEqEulerProductSchurSumsStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedWhittakerIntegral_eq_eulerProduct_schurSums : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CG E a), 1 ≤ a → π.IsUnitary →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π →
    ∃ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin a → ℂˣ) (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ)
      (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (π₀ : CuspSub E a) (ω : HChar E) (φ : Sm E a),
      (ℓ : ℕ) + 1 = a ∧
      (∀ w, Finset.univ.val.map (α w) = sat π w) ∧ CG.mk π₀ = π ∧ ω.IsUnitary ∧ π₀.HasCentChar ω ∧
      (φ ∈ π₀.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π₀) ∧ φ ≠ 0 ∧
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ Φ ≠ 0 ∧
      ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E a)), IsFundamentalDomain (GlobalTheory.CellDec.NE E a) 𝓕₀ μ →
        ∃ H : ℝ → ℝ, ContinuousWithinAt H (Set.Ioi 1) 1 ∧ 0 < H 1 ∧ ∀ x : ℝ, 1 < x → 0 < H x ∧
          ∫⁻ g in 𝓕₀, ‖GlobalTheory.RSTheta.rsPsi ℓ (GlobalTheory.JSW.whit φ.1) (GlobalTheory.JSW.whit φ.1) Φ J η g (g.val ℓ)‖ₑ * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ =
            ENNReal.ofReal (H x) * GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
              (fun w i => ((α w i : ℂˣ) : ℂ)) x := by
  first
  | exact @GlobalTheory.RSCell.lintegral_unfolded_eq
  | exact GlobalTheory.RSCell.lintegral_unfolded_eq
  | (intros; apply GlobalTheory.RSCell.lintegral_unfolded_eq <;> assumption)
end

