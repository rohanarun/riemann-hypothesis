module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeIsIntegralOverStandardLatticeStabilis
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2371
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelAmpleNearFibreFlatProjective
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SecondChernDegreeVanishesTrueSurfaces
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2712
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2727
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2606
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0232
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0825
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaVacuaConjugatesCmPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2724
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0269

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicDivOfBeta
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun

noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqTop.SqField

theorem gBig_and {Q Q' : GP} (h : GBig @Q) (h' : GBig @Q') :
    GBig fun {_ _ _ _} G μ C x b => Q G μ C x b ∧ Q' G μ C x b := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨a', ha'⟩ := h'
  refine ⟨max a a', fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h1⟩ := ha ε CF (le_of_max_le_left hCF)
  obtain ⟨C1, x1, h2⟩ := ha' ε CF (le_of_max_le_right hCF)
  refine ⟨max C0 C1, max x0 x1, fun C hC D large₂ he hx hR T Lc μ hμ G => ⟨?_, ?_⟩⟩
  · exact h1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ hμ G
  · exact h2 C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ hμ G

theorem isAlgebraic_norm {D : D7} {δ t0 : ℂ} {Q N : ℕ} {B : ℝ} {del : ℕ → ℝ} (hC : GlobalTheory.NormSum.CoordInt D N B Q del)
    (P : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q) (hP : P.Small N B) : IsAlgebraic ℚ ((P.norm : ℝ) : ℂ) := by
  have hco : ∀ h T, P.coord h T ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := fun h T => by
    obtain ⟨p, hp, hi⟩ := _root_.GlobalTheory.NormSum.exists_prime_integralOver D P.d h
    haveI : Fact p.Prime := ⟨hp⟩
    exact ((hC δ t0 p Q le_rfl P hP).2.2 h hi T).1
  have hsq : ∀ g, ((P.sq g : ℝ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := fun g => by
    unfold GlobalTheory.NormSum.Pair.sq
    rw [Complex.ofReal_sum]
    refine sum_mem fun T _ => ?_
    have e : ((‖P.coord g T‖ ^ 2 : ℝ) : ℂ) = P.coord g T * (starRingEnd ℂ) (P.coord g T) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [e]
    exact mul_mem (hco g T)
      (mem_algebraicClosure_iff.2 ((mem_algebraicClosure_iff.1 (hco g T)).algHom (starRingEnd ℂ).toRatAlgHom))
  have hterm : ∀ h : GlobalTheory.NormSum.Cls D P.d P.J,
      (((((GlobalTheory.NormSum.gam D P.J h.out : ℝ))⁻¹ * P.sq h.out : ℝ)) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := fun h => by
    rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
    exact mul_mem (inv_mem (natCast_mem _ _)) (hsq _)
  refine mem_algebraicClosure_iff.1 ?_
  unfold GlobalTheory.NormSum.Pair.norm
  by_cases hs : (Function.support fun h : GlobalTheory.NormSum.Cls D P.d P.J =>
      ((GlobalTheory.NormSum.gam D P.J h.out : ℝ))⁻¹ * P.sq h.out).Finite
  · rw [finsum_eq_sum _ hs, Complex.ofReal_sum]
    exact sum_mem fun h _ => hterm h
  · rw [finsum_of_infinite_support hs, Complex.ofReal_zero]
    exact zero_mem _

theorem isAlgebraic_div_of_beta {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {d s : ℕ} (hd : 0 < d)
    (hs : 1 ≤ s) (κ : I → ℕ) (Λ : PeriodPair) {x y : ℂ} (hx : x ≠ 0)
    (ha : IsAlgebraic ℚ (GlobalTheory.CMVal.beta E d s κ Λ x)) (hb : IsAlgebraic ℚ (GlobalTheory.CMVal.beta E d s κ Λ y)) :
    IsAlgebraic ℚ (y / x) := by
  have hC : (GlobalTheory.CMVal.C0 E d (2 * s) κ : ℂ) ≠ 0 := by exact_mod_cast (GlobalTheory.CMVal.cmValueConst_pos E hd (by omega) κ).ne'
  have hΔ : GlobalTheory.CMVal.latDisc Λ ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ ≠ 0 := pow_ne_zero _ (GlobalTheory.CMVal.latDisc_ne_zero Λ)
  have e : (y / x) ^ 12 = GlobalTheory.CMVal.beta E d s κ Λ y / GlobalTheory.CMVal.beta E d s κ Λ x := by
    unfold GlobalTheory.CMVal.beta
    field_simp
  refine IsAlgebraic.of_pow (n := 12) (by norm_num) ?_
  rw [e]
  exact mem_algebraicClosure_iff.1 (div_mem (mem_algebraicClosure_iff.2 hb) (mem_algebraicClosure_iff.2 ha))

theorem sqIn_of {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T)
    (hI : GlobalTheory.NormSum.IntSt) (hΛ : ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ)
    (hT : ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j → ∀ c, ∃ x, IsTor G i j s (fam G μ₀ i j c) x ∧ x ≠ 0 ∧
      ∀ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ →
        IsAlgebraic ℚ (GlobalTheory.CMVal.beta D.host.E D.host.d s (kap D sc.cGap i j s) Λ x))
    (hQ : GlobalTheory.NormSum.GoodLevel D (levQ G.pl))
    (hS : ∀ (δ t0 : ℂ) (Q : ℕ) (P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q) t (i j : Fin D.R.m) 𝔪, IsBottom G t i j 𝔪 P P' →
      P.Small (bigN D) (maxWt D sc.cGap) ∧ P'.Small (bigN D) (maxWt D sc.cGap)) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ GlobalTheory.BigTop.Fun.SqIn G μ₀ (algebraMap M ℂ) := by
  obtain ⟨C, -, hI⟩ := hI
  have hN : 1 ≤ bigN D := by have := D.R.m_add_three_le_k; unfold bigN; omega
  obtain ⟨-, del, -, hco, -⟩ := hI D (levQ G.pl) (bigN D) (maxWt D sc.cGap) (max 1 (Real.log D.host.rdE)) hQ hN
    (by exact_mod_cast le_max_left _ _) (le_max_left _ _) (le_max_right _ _)

  obtain ⟨Sn, hSn, hSa, hSb⟩ : ∃ Sn : Set ℂ, Sn.Finite ∧ (∀ z ∈ Sn, IsAlgebraic ℚ z) ∧
      (GlobalTheory.BigTop.Fun.BottomsWith G μ₀ (fun _ => True) → GlobalTheory.BigTop.Fun.BottomsWith G μ₀ (· ∈ Sn)) := by
    by_cases hb : GlobalTheory.BigTop.Fun.BottomsWith G μ₀ (fun _ => True)
    · obtain ⟨δ, t0, hb⟩ := hb
      choose P P' hP using hb
      refine ⟨Set.range (fun ij => ((P ij).norm : ℂ)) ∪ Set.range (fun ij => ((P' ij).norm : ℂ)),
        (Set.finite_range _).union (Set.finite_range _), ?_,
        fun _ => ⟨δ, t0, fun ij => ⟨P ij, P' ij, (hP ij).1, Or.inl ⟨ij, rfl⟩, Or.inr ⟨ij, rfl⟩⟩⟩⟩
      rintro z (⟨ij, rfl⟩ | ⟨ij, rfl⟩)
      · exact isAlgebraic_norm hco _ (hS δ t0 _ _ _ _ _ _ _ (hP ij).1).1
      · exact isAlgebraic_norm hco _ (hS δ t0 _ _ _ _ _ _ _ (hP ij).1).2
    · exact ⟨∅, Set.finite_empty, fun z hz => absurd hz (Set.notMem_empty z), fun h => absurd h hb⟩

  let St : Set ℂ := ⋃ (i : Fin D.R.m) (j : Fin D.R.m) (s ∈ Set.Icc 1 (halfRank D i j)) (c : Bool),
    {z | ∃ x y, IsTor G i j s (nuH G μ₀ i j) x ∧ IsTor G i j s (nuH G μ₀ i j * delOf Lc c) y ∧ z = y / x}
  have hSt : St.Finite := by
    refine Set.finite_iUnion fun i => Set.finite_iUnion fun j => (Set.finite_Icc _ _).biUnion fun s _ =>
      Set.finite_iUnion fun c => Set.Subsingleton.finite ?_
    rintro _ ⟨x, y, hx, hy, rfl⟩ _ ⟨x', y', hx', hy', rfl⟩
    rw [hx.2.unique hx'.2, hy.2.unique hy'.2]
  have hd : 0 < D.host.d := D.host.hypOdd.2.1.pos
  obtain ⟨Λ, hΛ⟩ := hΛ
  have hSta : ∀ z ∈ St, IsAlgebraic ℚ z := by
    intro z hz
    simp only [St, Set.mem_iUnion, Set.mem_setOf_eq] at hz
    obtain ⟨i, j, s, ⟨h1, h2⟩, c, x, y, hx, hy, rfl⟩ := hz
    obtain ⟨x0, hx0, hx00, ha⟩ := hT i j s h1 h2 none
    obtain ⟨x1, hx1, -, hb⟩ := hT i j s h1 h2 (some c)
    rw [hx.2.unique hx0.2, hy.2.unique hx1.2]
    exact isAlgebraic_div_of_beta hd h1 _ Λ hx00 (ha Λ hΛ) (hb Λ hΛ)
  let S : Set ℂ := Sn ∪ St
  haveI : Finite S := (hSn.union hSt).to_subtype
  have hmem : ∀ z ∈ S, z ∈ Set.range (algebraMap (IntermediateField.adjoin ℚ S) ℂ) := fun z hz =>
    ⟨⟨z, IntermediateField.subset_adjoin ℚ S hz⟩, rfl⟩
  refine ⟨IntermediateField.adjoin ℚ S, IntermediateField.finiteDimensional_adjoin fun z hz =>
    (Or.elim hz (hSa z) (hSta z)).isIntegral, ⟨fun h => ?_, fun i j s c x y h1 h2 hx hy => ?_⟩⟩
  · obtain ⟨δ, t0, b⟩ := hSb h
    exact ⟨δ, t0, fun ij => let ⟨P, P', a, b1, b2⟩ := b ij; ⟨P, P', a, hmem _ (Or.inl b1), hmem _ (Or.inl b2)⟩⟩
  · refine hmem _ (Or.inr ?_)
    simp only [St, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨i, j, s, ⟨h1, h2⟩, c, x, y, hx, hy, rfl⟩

end GlobalTheory.SqTop.SqField

namespace GlobalTheory.BigTop.Fun

end GlobalTheory.BigTop.Fun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorOfNefFibresAmple
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
open _root_.CategoryTheory.Limits

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AmpleNefFibZ

theorem exists_prime_le (P : Ideal ℤ) [P.IsPrime] :
    ∃ l : ℕ, l.Prime ∧ ∀ r : ℤ, r ∉ Ideal.span {(l : ℤ)} → r ∉ P := by
  obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P (Ideal.IsPrime.ne_top ‹_›)
  set m := Submodule.IsPrincipal.generator M
  have hmM : Ideal.span {m} = M := Submodule.IsPrincipal.span_singleton_generator M
  have hm0 : m ≠ 0 := by
    rintro h
    have := Ideal.bot_lt_of_maximal M Int.not_isField
    rw [← hmM, h, Ideal.span_singleton_eq_bot.2 rfl] at this
    exact lt_irrefl _ this
  have hmp : Prime m := (Ideal.span_singleton_prime hm0).1 (hmM ▸ hM.isPrime)
  refine ⟨m.natAbs, Int.prime_iff_natAbs_prime.1 hmp, fun r hr hrP => hr ?_⟩
  rw [Ideal.mem_span_singleton, Int.natAbs_dvd]
  rw [← Ideal.mem_span_singleton, hmM]
  exact hPM hrP

theorem isAmpleLB_tens_of_nefFib : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L A : HermLB p, NefFib L → IsAmpleLB A.B → IsAmpleLB (L.tens A).B := by
  intro k _ X _ p D hX L A hL hA
  haveI : Module.Finite ℤ k := hX.finite
  set s : X ⟶ Sp ℤ := p ≫ spMap (Int.castRingHom k) with hs_def
  have hsZ : s = ShFam.Pad.toSpZ X := specZIsTerminal.hom_ext _ _
  have hP : IsProjOver s := hsZ ▸ ShFam.Pad.isProjOver_toSpZ hX.isProjOver
  have hPB : AbLaw.IsProjBy s := (ProjSpace.isProjBy_iff_isProjOver s).2 hP
  haveI : IsProper s := hsZ ▸ FibreProj.isProper_of_isArithVar (ShFam.Pad.isArithVar_toSpZ hX)
  have hM : (L.tens A).B.IsLB := (L.tens A).isLB
  haveI : IsProper (Over.mk s).hom := ‹IsProper s›
  refine (relAmple_iff_isAmpleLB_of_isAffine (Over.mk s) hM).1 ?_
  refine AmpleLocal.relAmple_of_locally _ (Over.mk s) _ hM inferInstance inferInstance fun P => ?_
  obtain ⟨l, hl, hlP⟩ := @exists_prime_le P.asIdeal P.isPrime
  haveI : Fact l.Prime := ⟨hl⟩
  have F := _root_.GlobalTheory.AmpleFibre.isAmpleLB_fibre k X p D hX L A hL hA l
  have hFib : Out.RelAmple ((Over.pullback (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod l))))).obj (Over.mk s))
      ((L.tens A).B.pull (pullback.fst s (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod l)))))) := by
    haveI : IsProper ((Over.pullback (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod l))))).obj (Over.mk s)).hom :=
      inferInstanceAs (IsProper (pullback.snd s _))
    exact (relAmple_iff_isAmpleLB_of_isAffine _ (LB.isLB_pull hM _)).2 F
  have hfrac : ∀ y : ZMod l, ∃ a b : ℤ, Int.castRingHom (ZMod l) b ≠ 0 ∧
      y * Int.castRingHom (ZMod l) b = Int.castRingHom (ZMod l) a :=
    fun y => ⟨(y.val : ℤ), 1, by simp, by simp⟩
  obtain ⟨r, hr, hA'⟩ := AmpleNear.relAmple_near_fibre ℤ (Over.mk s) (L.tens A).B hX.flat hPB hM (ZMod l)
    (Int.castRingHom (ZMod l)) hfrac hFib
  have hrl : r ∉ Ideal.span {(l : ℤ)} := by
    rw [Ideal.mem_span_singleton]
    intro h
    exact hr ((ZMod.intCast_zmod_eq_zero_iff_dvd r l).2 h)
  let U : (Spec (CommRingCat.of ℤ)).Opens := PrimeSpectrum.basicOpen r
  haveI : IsAffine U.toScheme := IsAffineOpen.Spec_basicOpen (R := CommRingCat.of ℤ) r
  exact ⟨U, hlP r hrl, AmpleFibres.relAmple_restrict U (Over.mk s) hM hA'⟩

end GlobalTheory.AmpleNefFibZ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeCharMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareChars

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem isHeckeChar_mul' {c c' : (AE D)ˣ →* Circle} (h : IsHeckeChar D c) (h' : IsHeckeChar D c') :
    IsHeckeChar D (c * c') :=
  ⟨h.1.mul h'.1, fun x => by rw [MonoidHom.mul_apply, h.2 x, h'.2 x, mul_one]⟩

theorem isHeckeChar_pow' {c : (AE D)ˣ →* Circle} (h : IsHeckeChar D c) (n : ℕ) : IsHeckeChar D (c ^ n) :=
  ⟨h.1.pow n, fun x => by rw [MonoidHom.pow_apply, h.2 x, one_pow]⟩

theorem resEta_pow' {c : (AE D)ˣ →* Circle} (h : ResEta D c 1) (n : ℕ) : ResEta D (c ^ n) n :=
  ⟨h.1, fun e he a => by rw [MonoidHom.pow_apply, h.2 e he a, pow_one]⟩

theorem chi_hecke_res (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (i : Fin D.R.m) :
    IsHeckeChar D (G.ch.chi (D.R.m - i)) ∧ ResEta D (G.ch.chi (D.R.m - i)) 0 := by
  have h1 : 1 ≤ D.R.m - (i : ℕ) := by omega
  have h2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
  have hc := G.ch.chi_eq _ h1 h2
  refine ⟨⟨hc.1.1, hc.1.2⟩, ?_⟩
  have hres := GlobalTheory.Mem.EtaTilde.isEta_res D L.eta L.C.eta hL.eta L.C.isEta
  refine ⟨⟨_, hres⟩, fun η _ a => ?_⟩
  rw [pow_zero, GlobalTheory.GridWeil.triv_base hc (G.ch.triv _ h1 h2) a]

theorem rank_parity (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (i j : Fin D.R.m) :
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j) % 2 = (spW G i j).rank % 2 ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j) % 2 = (spW₁ G i j).rank % 2 := by
  have r : ∀ a b, a ≤ D.R.m → b ≤ D.R.m → (G.V (.grid a b)).rank = rankV D a b :=
    fun a b ha hb => (node_isV G hL (X := .grid a b) ⟨ha, hb⟩).rank
  have hi := i.2
  have hj := j.2
  have e1 : (spW G i j).rank = rankV D (i + 1) (j + 1) := r _ _ (by omega) (by omega)
  have e2 : (spW₁ G i j).rank = rankV D i j := r _ _ (by omega) (by omega)
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps
  rw [e1, e2]
  obtain ⟨a, ha⟩ := D.R.t_odd
  obtain ⟨b, hb⟩ := odd_sLen D
  simp only [rankV, ha, hb]
  constructor
  · rw [Nat.mod_mod]; ring_nf; omega
  · rw [Nat.mod_mod]

end GlobalTheory.SquareChars

namespace GlobalTheory.SquareChars

theorem square_chars : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), SquareStanding G t →
      GlobalTheory.LFun.IsHecke D.host.F D.host.E (beta G i j : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) ∧
      GlobalTheory.LFun.IsHecke D.host.F D.host.E (alpha G t i j : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) ∧
      GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F) : D.host.F →* AF D.host.F)).range
        (beta G i j : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (spW G i j).rank ∧
      GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F) : D.host.F →* AF D.host.F)).range
        (alpha G t i j : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (spW₁ G i j).rank := by
  intro D T L sc G μ₀ hL t i j _
  obtain ⟨hχ, hχ0⟩ := chi_hecke_res G hL i
  have hμ := GlobalTheory.HeckeCharacterRestriction.isHecke_mu hL t j
  have hμ0 := GlobalTheory.HeckeCharacterRestriction.resEta_mu hL t j
  have hη := isHeckeChar_pow' hL.eta.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j)
  have hη1 := resEta_pow' (GlobalTheory.HeckeCharacterRestriction.resEta_eta hL) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j)
  obtain ⟨p1, p2⟩ := rank_parity G hL i j
  have hβ : ResEta D (beta G i j) (spW G i j).rank :=
    resEta_parity (resEta_mul hχ0 hη1) (by rw [zero_add]; exact p1)
  have hα : ResEta D (alpha G t i j) (spW₁ G i j).rank :=
    resEta_parity (resEta_mul hμ0 hη1) (by rw [zero_add]; exact p2)
  have h2 : Module.finrank D.host.F D.host.E = 2 := D.sp.cm.deg2
  exact ⟨isHeckeChar_mul' hχ hη, isHeckeChar_mul' hμ hη,
    _root_.GlobalTheory.LFun.resEtaPow_of_resEta D.host.F D.host.E h2 _ _ hβ, _root_.GlobalTheory.LFun.resEtaPow_of_resEta D.host.F D.host.E h2 _ _ hα⟩

end GlobalTheory.SquareChars
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyCompIffAndDegreeMul
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AV.AbVar.isIsogeny_comp_iff_and_deg_comp : ∀ (K : Type) [Field K] (A B C : AbVar K) (f : A ⟶ B) (g : B ⟶ C),
    A.dim = B.dim → B.dim = C.dim →
      (IsIsogeny (f ≫ g) ↔ IsIsogeny f ∧ IsIsogeny g) ∧ deg (f ≫ g) = deg f * deg g := by
  intro K _ A B C f g hAB hBC
  have hleft : (f ≫ g).hom.left = f.hom.left ≫ g.hom.left := by
    rw [comp_hom, Over.comp_left]
  have key : IsIsogeny (f ≫ g) ↔ IsIsogeny f ∧ IsIsogeny g := by
    constructor
    · rintro ⟨hfin, hsurj⟩
      have hs2 : Surjective (f.hom.left ≫ g.hom.left) := by rw [← hleft]; exact hsurj
      have hgs : Surjective g.hom.left := Surjective.of_comp f.hom.left g.hom.left
      have hgf : IsFinite g.hom.left := _root_.GlobalTheory.AV.AbVar.isFinite_of_surjective_of_dim_eq K B C g hBC hgs
      have hker : Finite (ptMap (f ≫ g)).ker := (_root_.GlobalTheory.AV.AbVar.isFinite_iff_finite_ker K A C (f ≫ g)).1 hfin
      have hle : (ptMap f).ker ≤ (ptMap (f ≫ g)).ker := by
        intro x hx
        rw [MonoidHom.mem_ker] at hx ⊢
        have hx' : x ≫ f.hom = 1 := hx
        show x ≫ (f ≫ g).hom = 1
        rw [comp_hom, ← Category.assoc, hx', MonObj.one_comp]
      have hfk : Finite (ptMap f).ker :=
        Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
      have hff : IsFinite f.hom.left := (_root_.GlobalTheory.AV.AbVar.isFinite_iff_finite_ker K A B f).2 hfk
      exact ⟨⟨hff, _root_.GlobalTheory.AV.AbVar.surjective_of_isFinite_of_dim_eq K A B f hAB hff⟩, ⟨hgf, hgs⟩⟩
    · rintro ⟨hf, hg⟩
      exact (_root_.GlobalTheory.AV.AbVar.isIsogeny_comp_and_deg_comp K A B C f g hf hg).1
  refine ⟨key, ?_⟩
  by_cases h : IsIsogeny f ∧ IsIsogeny g
  · exact (_root_.GlobalTheory.AV.AbVar.isIsogeny_comp_and_deg_comp K A B C f g h.1 h.2).2
  · have h0 : deg (f ≫ g) = 0 := by
      unfold deg; rw [if_neg (fun h' => h (key.1 h'))]
    rw [h0]
    rcases not_and_or.1 h with hf | hg
    · have : deg f = 0 := by unfold deg; rw [if_neg hf]
      rw [this, zero_mul]
    · have : deg g = 0 := by unfold deg; rw [if_neg hg]
      rw [this, mul_zero]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMapOfNatMultipleFormalGroupLaw
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz

theorem Chart.zero_app_eq {p : ℕ} [Fact p.Prime] {k : Type} [CommRing k] (G : PDivGroup p k)
    (n : ℕ) (a : G.A n) :
    (0 : G ⟶ G).app n a = algebraMap k _ (Coalgebra.counit (R := k) a) := by
  have h := congrArg (fun u : WithConv (G.A n →ₐ[k] G.A n) => u.ofConv a)
    (map_one (toPts (R := k) (A := G.A n) (C := G.A n)))
  simp only [toPts_ofConv] at h
  exact h.trans (AlgHom.convOne_apply _)

theorem Chart.isMapOf_nmul : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] (d : ℕ)
    (G : PDivGroup p k) (c : Katz.Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k),
    c.IsLawOf μ → ∀ j : ℕ, c.IsMapOf c ((j : ℤ_[p]) • 𝟙 G) (nmul μ j) := by
  intro p _ k _ d G c μ hμ j
  induction j with
  | zero =>
    intro n i
    rw [Nat.cast_zero, zero_smul, Chart.zero_app_eq, c.aug, map_zero]
    show c.ev n ((fun _ => (0 : MvPowerSeries (Fin d) k)) i) = 0
    exact map_zero _
  | succ j ih =>
    have hX : c.IsMapOf c (𝟙 G) (fun i => (X i : MvPowerSeries (Fin d) k)) := fun n i => by
      rw [Chart.ev_X, id_app]; rfl
    have e1 : ((j + 1 : ℕ) : ℤ_[p]) • 𝟙 G = (j : ℤ_[p]) • 𝟙 G + 𝟙 G := by
      rw [Nat.cast_succ, add_smul, one_smul]
    have e2 : nmul μ (j + 1) = op μ (nmul μ j) (fun i => X i) :=
      Function.iterate_succ_apply' _ _ _
    rw [e1, e2]
    exact Chart.isMapOf_add p k d d G G c c μ _ _ _ _ hμ ih hX

end GlobalTheory.Katz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetOperatorRationalFormConjEqConjTable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.JetDescent

theorem coe_lift_of_mem (M : IntermediateField ℚ ℂ) (x : ℂ) (hx : x ∈ M) : Formalism.MainNotions.TaylorLogMetric.liftM M x = ⟨x, hx⟩ := by
  unfold Formalism.MainNotions.TaylorLogMetric.liftM
  exact dif_pos hx

theorem mapVV_rational_form_conj : ∀ {D : D7} {a b : ℕ} (lam : D.what₂.Tau → DomWeight a) (lam' : D.what₂.Tau → DomWeight b) (n : D.what₂.Tau → ℕ)
    (J : (Formalism.L2.Ker.DVar D.what₂.Tau a b →₀ ℕ) → ℂ) (σ : D.what₂.LL →+* ℂ) (ρ' : Qbar →ₐ[ℚ] ℂ)
    (f : VV D.what₂.LL lam →ₗ[D.what₂.LL] VV D.what₂.LL lam'), Formalism.L2.Ker.JetInVV ℂ lam lam' n → (∀ m, J m ∈ Qbar) →
    (∀ x, Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (D.what₂.embLL x) = σ x) →
    (∀ u, Formalism.L2.Ker.jetOp lam lam' J n (GlobalTheory.CoefModel.mapVV D.what₂.embLL lam u) = GlobalTheory.CoefModel.mapVV D.what₂.embLL lam' (f u)) →
    ∀ u, GlobalTheory.CoefModel.mapVV σ lam' (f u) =
      Formalism.L2.Ker.jetOp lam lam' (fun m => Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (J m)) n (GlobalTheory.CoefModel.mapVV σ lam u) := by
  intro D a b lam lam' n J σ ρ' f hV hJ hσ hf u
  have halg : ∀ x : D.what₂.LL, D.what₂.embLL x ∈ Qbar := fun x => by
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.what₂.embLL.toRatAlgHom
  let e : D.what₂.LL →+* Qbar := D.what₂.embLL.codRestrict Qbar halg
  let i : Qbar →+* ℂ := algebraMap Qbar ℂ
  let r : Qbar →+* ℂ := ρ'
  let Jq : (Formalism.L2.Ker.DVar D.what₂.Tau a b →₀ ℕ) → Qbar := fun m => ⟨J m, hJ m⟩
  have hie : i.comp e = D.what₂.embLL := RingHom.ext fun _ => rfl
  have hre : r.comp e = σ := RingHom.ext fun x => by
    rw [← hσ x]
    unfold Formalism.MainNotions.StandardLatticesGL3.cj
    rw [coe_lift_of_mem _ _ (halg x)]
    rfl
  have hJi : (fun m => i (Jq m)) = J := funext fun _ => rfl
  have hJr : (fun m => r (Jq m)) = fun m => Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (J m) := funext fun m => by
    unfold Formalism.MainNotions.StandardLatticesGL3.cj
    rw [coe_lift_of_mem _ _ (hJ m)]
    rfl
  have h1 : Formalism.L2.Ker.jetMap J n (MvPolynomial.map D.what₂.embLL u.1) = MvPolynomial.map D.what₂.embLL (f u).1 := by
    have h := congrArg Subtype.val (hf u)
    rw [Formalism.L2.Ker.jetOp_coe lam lam' n hV] at h
    exact h
  have h2 : Formalism.L2.Ker.jetMap Jq n (MvPolynomial.map e u.1) = MvPolynomial.map e (f u).1 := by
    apply MvPolynomial.map_injective i i.injective
    rw [Formalism.L2.Ker.map_jetMap, MvPolynomial.map_map, MvPolynomial.map_map, hie, hJi]
    exact h1
  have h3 := congrArg (MvPolynomial.map r) h2
  rw [Formalism.L2.Ker.map_jetMap, MvPolynomial.map_map, MvPolynomial.map_map, hre, hJr] at h3
  apply Subtype.ext
  rw [Formalism.L2.Ker.jetOp_coe lam lam' n hV]
  exact h3.symm

end GlobalTheory.JetDescent
end

