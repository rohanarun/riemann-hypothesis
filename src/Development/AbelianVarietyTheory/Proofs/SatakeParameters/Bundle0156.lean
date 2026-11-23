module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0152
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EOpEqAsAlgebraHom
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnitaryCarries
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0151
public import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0935
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDeltaPsi
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBaseLevelVectorInGoodAlgebraicFormsSpan
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3

theorem exists_part_level_vector : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → ∀ j c, R.Wc' j c ≠ ⊥ → ∃ w ∈ R.Wc' j c, w ≠ 0 ∧ w ∈ R.toRealDat.WS F.lv2 false j (sg0 D A3.A) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hW hEx hSch s hOk hGG hU j c hne
  obtain ⟨hCoreF, hSF, -, -, -, hWc, -⟩ := _root_.GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hW
  have hCore := hCoreF hEx
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  obtain ⟨h, -, -, -, hsup, hstab, -, -⟩ := _root_.GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt R.toRealDat F.lv2 hCore hSch hX R.SF hSF j
  obtain ⟨hid, -, -, -⟩ := eH_laws R.toRealDat F.lv2 hCore hX j
  have hfix : ∀ u ∈ Wcc R.toRealDat R.SF j c, eH R.toRealDat j u = u := by
    intro u hu
    have hr : u ∈ LinearMap.range (eH R.toRealDat j) := hsup ▸ (le_iSup (fun c => Wcc R.toRealDat R.SF j c) c) hu
    obtain ⟨x, rfl⟩ := hr
    rw [← Module.End.mul_apply, hid]
  rw [hWc] at hne ⊢
  obtain ⟨u, huU, hu0, hup⟩ := _root_.GlobalTheory.Hk3.exists_level_vector (sg0 D A3.A) A3.A.X F.P0 F.ψ0⁻¹ (R.gW j (sg0 D A3.A))
    (Wcc R.toRealDat R.SF j c) hX hGG (fun g => hstab c g) hne (fun u hu => by
      have := hfix u hu
      simpa [eH, RealDat.eC] using this)
  refine ⟨u, huU, hu0, ?_⟩
  have hlev := (_root_.GlobalTheory.Hk3.goodForms_baseLevel R.toRealDat F.lv2 hCore hX j u).2 ⟨hfix u huU, hup⟩
  have hL := GlobalTheory.LevelForms.levelW_of_irr R.toRealDat F.lv2 hX hU hCore.models.HW
  rw [hL false j (sg0 D A3.A)]
  exact hlev

end GlobalTheory.Hk3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLimitDvdUniformizerPowCauchyStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_limit_dvdUniformizerPow_cauchy : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ a : ℕ → L, (∀ k, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (a (k + 1) - a k)) →
    ∃ b : L, ∀ k, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (b - a k) := by
  first | exact @GlobalTheory.Hk3.IntWittBase.exists_limit_dvdPow | exact GlobalTheory.Hk3.IntWittBase.exists_limit_dvdPow | (intros; apply GlobalTheory.Hk3.IntWittBase.exists_limit_dvdPow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsStdSplit
section
open NumberField IsDedekindDomain Matrix

noncomputable section

namespace GlobalTheory.ColPeriod

open _root_.Formalism.L2.Col Formalism.HermitianLatticesTheory GlobalTheory.StdReps

theorem splitNonConj_vG {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (i : Fin 2) :
    GlobalTheory.IndefiniteRowSideFullHecke.StandardDeterminantUnit.SplitNonConj (Pr.vG i) := by
  intro P hP Q hQ h
  have h1 : cO X.E (Pr.piG i) ∈ Q.asIdeal := decoFin_mem_of_mem_divs hQ
  have h2 : cO X.E (Pr.piG i) ∈ P.asIdeal := decoFin_mem_of_mem_divs hP
  rw [h, mem_conjP, cO_cO] at h1
  obtain ⟨a, b, e⟩ := hPr.piG_cop i
  apply one_notMem P
  rw [← e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

theorem exists_std_split {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST : Finset (HeightOneSpectrum (𝓞 E))}
    (hST : GlobalTheory.IndefiniteRowSideFullHecke.StandardDeterminantUnit.SplitNonConj ST) {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) :
    ∃ γ : UF E n, ∀ P ∈ ST, localization₂ P.asIdeal (gmap γ.1 N) = stdAt E n P ∧
      localization₂ (conjPrime₂ P).asIdeal (gmap γ.1 N) = stdAt E n (conjPrime₂ P) := by
  obtain ⟨g, hg, hc⟩ := exists_unitary_carries hST (by first | exact hN | exact hN.1)
  let f : Sp E n ≃ₗ[E] Sp E n := Matrix.toLin'OfInv (M := gᴴ) (M' := g) hg (mul_eq_one_comm.1 hg)
  have hf : ∀ x, f x = g *ᵥ x := fun x => rfl
  have hU : f ∈ UF E n := by
    intro x y
    rw [hf, hf, hStd_apply, hStd_apply]
    change star (g *ᵥ x) ⬝ᵥ (g *ᵥ y) = star x ⬝ᵥ y
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hg, one_mulVec]
  have huni : IsUnimodular (hStd E n) (gmap f N) := by
    have e : dual (hStd E n) N = N := hN.2
    change dual (hStd E n) (gmap f N) = gmap f N
    rw [dual_gmap f hU, e]
  refine ⟨⟨f, hU⟩, fun P hP => ?_⟩
  have h : localization₂ P.asIdeal (gmap f N) = stdAt E n P := by
    ext x
    rw [mem_localization_gmap, ← (hc P hP).2, ← hf, LinearEquiv.apply_symm_apply]
  exact ⟨h, le_antisymm (localization_conj_le_of_le stdLat_lattice.fg stdLat_unimodular huni h.ge)
    (localization_conj_le_of_le (gmap_lattice f N hN.1).fg huni stdLat_unimodular h.le)⟩

theorem stdMove : StdMove := by
  intro X Pr hPr i n N hN
  obtain ⟨γ, hγ⟩ := exists_std_split (splitNonConj_vG hPr i) hN
  refine ⟨γ, fun Q hQ => ?_⟩
  have h0 : X.conjO (Pr.piG i) ≠ 0 := by
    intro h
    have h1 := hPr.piG_norm i
    rw [h, mul_zero] at h1
    exact (hPr.g_prime i).ne_zero (by exact_mod_cast h1.symm)
  rw [← hPr.piG_norm i] at hQ
  rcases Q.isPrime.mem_or_mem hQ with h | h
  · have hm : conjPrime₂ Q ∈ Pr.vG i := (Formalism.L2.Col.mem_divs h0 _).2 (by
      change cO X.E (cO X.E (Pr.piG i)) ∈ Q.asIdeal
      rwa [cO_cO])
    have hcc : conjPrime₂ (conjPrime₂ Q) = Q := by
      ext x
      rw [mem_conjP, mem_conjP, cO_cO]
    have := (hγ _ hm).2
    rwa [hcc] at this
  · exact (hγ _ ((Formalism.L2.Col.mem_divs h0 _).2 h)).1

end GlobalTheory.ColPeriod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSupercuspidalTypeCharacterZmodPow
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong

open Matrix

namespace GlobalTheory.CuspType

variable {R : Type} [CommRing R]

theorem mem_ker_map_mk_iff {a : ℕ} (I : Ideal R) (g : GL (Fin a) R) :
    g ∈ (Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk I)).ker ↔
      ∀ i j, (g : Matrix (Fin a) (Fin a) R) i j - (1 : Matrix (Fin a) (Fin a) R) i j ∈ I := by
  rw [MonoidHom.mem_ker, Units.ext_iff]
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    rw [GeneralLinearGroup.map_apply] at this
    rw [← Ideal.Quotient.eq, this]
    by_cases hij : i = j <;> simp only [Units.val_one, Matrix.one_apply, hij, ↓reduceIte, map_one, map_zero]
  · intro h
    ext i j
    rw [GeneralLinearGroup.map_apply]
    have := Ideal.Quotient.eq.2 (h i j)
    rw [this]
    by_cases hij : i = j <;> simp only [Units.val_one, Matrix.one_apply, hij, ↓reduceIte, map_one, map_zero]

theorem exists_eq_one_add_smul {a : ℕ} (c : R) (g : GL (Fin a) R)
    (hg : g ∈ (Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk (Ideal.span {c}))).ker) :
    ∃ x : Matrix (Fin a) (Fin a) R, (g : Matrix (Fin a) (Fin a) R) = 1 + c • x := by
  have h := (mem_ker_map_mk_iff _ g).1 hg
  choose x hx using fun i j => Ideal.mem_span_singleton'.1 (h i j)
  refine ⟨Matrix.of fun i j => x i j, ?_⟩
  ext i j
  have := hx i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_comm, this]
  ring

def powChar (n : ℕ) [NeZero n] (ζ : ℂˣ) (hζ : ζ ^ n = 1) : Multiplicative (ZMod n) →* ℂˣ where
  toFun x := ζ ^ (Multiplicative.toAdd x).val
  map_one' := by simp
  map_mul' x y := by
    rw [toAdd_mul, ZMod.val_add, ← pow_add]
    conv_rhs => rw [← Nat.mod_add_div ((Multiplicative.toAdd x).val + (Multiplicative.toAdd y).val) n,
      pow_add, pow_mul, hζ, one_pow, mul_one]

theorem powChar_apply (n : ℕ) [NeZero n] (ζ : ℂˣ) (hζ : ζ ^ n = 1) (x : Multiplicative (ZMod n)) :
    powChar n ζ hζ x = ζ ^ (Multiplicative.toAdd x).val := rfl

theorem conj_vecMulVec {K : Type} [Field K] {a : ℕ} (W : Submodule K (Fin a → K))
    (g g' : Matrix (Fin a) (Fin a) K) (hgg' : g * g' = 1) (p q : Fin a → K)
    (hp : g *ᵥ p ∈ W) (hq : ∀ y, g *ᵥ y ∈ W → q ⬝ᵥ y = 0) :
    (∀ v, (g * vecMulVec p q * g') *ᵥ v ∈ W) ∧ ∀ v ∈ W, (g * vecMulVec p q * g') *ᵥ v = 0 := by
  have key : ∀ v, (g * vecMulVec p q * g') *ᵥ v = (q ⬝ᵥ (g' *ᵥ v)) • (g *ᵥ p) := by
    intro v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
      Matrix.mulVec_smul]
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · rw [key]; exact W.smul_mem _ hp
  · rw [key, hq _ (by rw [Matrix.mulVec_mulVec, hgg', Matrix.one_mulVec]; exact hv), zero_smul]

end GlobalTheory.CuspType

namespace GlobalTheory.CuspType

theorem exists_type : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a l : ℕ), l.Prime → (l : 𝓞 E) ∈ w.asIdeal → 1 ≤ a → ∀ N ∈ nhds (1 : GL (Fin a) (w.adicCompletion E)), ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ ∃ (J : Subgroup (GL (Fin a) (w.adicCompletion E))) (lam : J →* Multiplicative (ZMod (l ^ m))), IsOpen (J : Set (GL (Fin a) (w.adicCompletion E))) ∧ IsCompact (J : Set (GL (Fin a) (w.adicCompletion E))) ∧ (J : Set (GL (Fin a) (w.adicCompletion E))) ⊆ N ∧ (∀ g ∈ J, IsOfFinOrder g → g = 1) ∧ IsOpen (lam.ker : Set J) ∧ ∀ ζ : ℂˣ, ζ ^ (l ^ m) = 1 → ζ ≠ 1 → ∀ (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (v : σ.V), v ≠ 0 → (∀ g : J, σ.ρ g v = ((ζ ^ (Multiplicative.toAdd (lam g)).val : ℂˣ) : ℂ) • v) → GlobalTheory.SmGL.IsCuspidal σ.ρ := by
  intro E _ _ w a l hl hlw ha N hN m₀
  classical
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  haveI : CharZero (w.adicCompletionIntegers E) :=
    (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)).charZero
  haveI : Finite (IsLocalRing.ResidueField (w.adicCompletionIntegers E)) :=
    Formalism.UG.P.glint_finite_residueField w
  have hlR : ¬ IsUnit (l : w.adicCompletionIntegers E) := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := E) w (l : 𝓞 E)
    have h3 := (w.valuation_lt_one_iff_mem (K := E) (l : 𝓞 E)).2 hlw
    simp only [map_natCast] at h2 h3 ⊢
    push_cast at h2 h3 ⊢
    rw [h2]; exact h3.ne
  obtain ⟨hOC, hsmall⟩ := GlobalTheory.T.adicCompletion_congruenceSubgroups_open_compact_small E w a l hl hlw
  obtain ⟨m, hmN, hm⟩ := ((hsmall N hN).and (Filter.eventually_ge_atTop (max m₀ 2))).exists
  refine ⟨m, le_trans (le_max_left _ _) hm, ?_⟩
  have hm2 : 2 ≤ m := le_trans (le_max_right _ _) hm

  let ι := Matrix.GeneralLinearGroup.map (n := Fin a)
    (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))
  have hι : Function.Injective ι := by
    intro g h hgh
    refine Units.ext (Matrix.ext fun i j => ?_)
    have := congrArg (fun g : GL (Fin a) (w.adicCompletion E) => g.1 i j) hgh
    simp only [ι, GeneralLinearGroup.map_apply] at this
    exact Subtype.ext this

  have hc : ((l : w.adicCompletionIntegers E) ^ m) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.ne_zero)
  obtain ⟨B₀, hB₀⟩ := _root_.GlobalTheory.exists_matrix_no_invariant_subspace (IsLocalRing.ResidueField (w.adicCompletionIntegers E)) a ha
  let B : Matrix (Fin a) (Fin a) (w.adicCompletionIntegers E) :=
    B₀.map (Function.surjInv IsLocalRing.residue_surjective)
  have hB : B.map (IsLocalRing.residue _) = B₀ := by
    ext i j; exact Function.surjInv_eq _ _
  obtain ⟨φ, hφ1, hφ0⟩ := _root_.GlobalTheory.exists_addHom_zmod_pow_one_of_not_isUnit (w.adicCompletionIntegers E) l m hl hlR
  obtain ⟨lam₀, hlam₀⟩ := GlobalTheory.T.exists_congruenceKernel_trace_character (w.adicCompletionIntegers E) (ZMod (l ^ m)) a
    ((l : w.adicCompletionIntegers E) ^ m) hc φ hφ0 B
  let K₀ := (Matrix.GeneralLinearGroup.map (n := Fin a)
    (Ideal.Quotient.mk (Ideal.span {(l : w.adicCompletionIntegers E) ^ m}))).ker
  let e := K₀.equivMapOfInjective ι hι
  refine ⟨K₀.map ι, lam₀.comp e.symm.toMonoidHom, (hOC m).1, (hOC m).2, hmN, ?_, ?_, ?_⟩
  ·
    intro g hg hfin
    obtain ⟨g₀, hg₀, rfl⟩ := Subgroup.mem_map.1 hg
    obtain ⟨x, hx⟩ := exists_eq_one_add_smul _ g₀ hg₀
    obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
    have h1 : g₀ ^ n = 1 := hι (by rw [map_pow, hpow, map_one])
    have h2 : (1 + ((l : w.adicCompletionIntegers E) ^ m) • x) ^ n = 1 := by
      rw [← hx, ← Units.val_pow_eq_pow_val, h1, Units.val_one]
    have h3 := _root_.GlobalTheory.principalCongruence_torsionFree _ l m a hl hlR hm2 x n hn h2
    have : g₀ = 1 := Units.ext (by rw [hx, h3, smul_zero, add_zero, Units.val_one])
    rw [this, map_one]
  ·
    let J₂ := (Matrix.GeneralLinearGroup.map (n := Fin a)
      (Ideal.Quotient.mk (Ideal.span {(l : w.adicCompletionIntegers E) ^ (2 * m)}))).ker.map ι
    refine Subgroup.isOpen_mono (H₁ := J₂.comap (K₀.map ι).subtype) ?_
      ((hOC (2 * m)).1.preimage continuous_subtype_val)
    intro y hy
    obtain ⟨g₀, hg₀, hgy⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hy)
    obtain ⟨x, hx⟩ := exists_eq_one_add_smul _ g₀ hg₀
    have hz : ((e.symm y : K₀) : GL (Fin a) (w.adicCompletionIntegers E)) = g₀ := by
      apply hι
      rw [hgy, ← Subgroup.coe_equivMapOfInjective_apply K₀ ι hι, MulEquiv.apply_symm_apply]
      rfl
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      hlam₀ (e.symm y) (((l : w.adicCompletionIntegers E) ^ m) • x)
        (by rw [hz, hx, smul_smul, ← pow_add, two_mul]),
      Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, hφ0, ofAdd_zero]
  ·
    intro ζ hζ hζ1 σ v hv hev
    haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
    haveI : Fact (1 < l ^ m) := ⟨Nat.one_lt_pow (by omega) hl.one_lt⟩
    refine ⟨σ.smooth, fun s d e' he => ?_⟩
    obtain ⟨W, hW0, hWT, hWcrit⟩ := GlobalTheory.T.unipotent_radical_flag_stabilizer (w.adicCompletion E) a s d e' he
    refine _root_.GlobalTheory.jacquet_subsingleton_of_char_nontrivial_on_conj (GL (Fin a) (w.adicCompletion E)) σ.V σ.ρ σ.irred
      (GlobalTheory.SmGL.unipRad (w.adicCompletion E) e') (K₀.map ι)
      ((powChar (l ^ m) ζ hζ).comp (lam₀.comp e.symm.toMonoidHom)) v hv (fun h => hev h) ?_
    intro g
    have hgg : (g : Matrix (Fin a) (Fin a) (w.adicCompletion E)) * ((g⁻¹ : GL _ _) : Matrix _ _ _) = 1 :=
      Units.mul_inv g
    let W' : Submodule (w.adicCompletion E) (Fin a → w.adicCompletion E) :=
      W.comap (Matrix.toLin' (g : Matrix (Fin a) (Fin a) (w.adicCompletion E)))
    have hmem : ∀ y, y ∈ W' ↔ (g : Matrix (Fin a) (Fin a) (w.adicCompletion E)) *ᵥ y ∈ W := fun y => by
      simp [W', Matrix.toLin'_apply]
    have hW'0 : W' ≠ ⊥ := by
      obtain ⟨y, hyW, hy0⟩ := (Submodule.ne_bot_iff W).1 hW0
      refine (Submodule.ne_bot_iff W').2 ⟨((g⁻¹ : GL _ _) : Matrix _ _ _) *ᵥ y, ?_, ?_⟩
      · rw [hmem, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]; exact hyW
      · intro h0; apply hy0
        have := congrArg ((g : Matrix (Fin a) (Fin a) (w.adicCompletion E)) *ᵥ ·) h0
        simpa [Matrix.mulVec_mulVec, hgg] using this
    have hW'T : W' ≠ ⊤ := by
      intro htop; apply hWT; rw [eq_top_iff]; intro y _
      have : ((g⁻¹ : GL _ _) : Matrix _ _ _) *ᵥ y ∈ W' := htop ▸ Submodule.mem_top
      rw [hmem, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec] at this
      exact this
    obtain ⟨wv, f, hw, hf, hu⟩ := _root_.GlobalTheory.Cong.exists_integral_unit_pairing_of_irreducible_reduction (w.adicCompletionIntegers E) (w.adicCompletion E) a B
      (by rw [hB]; exact hB₀) W' hW'0 hW'T
    have hinj := IsFractionRing.injective (w.adicCompletionIntegers E) (w.adicCompletion E)
    have hfw : f ⬝ᵥ wv = 0 := by
      apply hinj
      rw [RingHom.map_dotProduct, map_zero]
      exact hf _ hw
    let x : Matrix (Fin a) (Fin a) (w.adicCompletionIntegers E) :=
      ((hu.unit⁻¹ : (w.adicCompletionIntegers E)ˣ) : w.adicCompletionIntegers E) • vecMulVec wv f
    have hxx : x * x = 0 := by
      simp only [x, Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_vecMulVec, hfw, zero_smul]
      ext i j; simp [vecMulVec_apply]
    have hyy : (((l : w.adicCompletionIntegers E) ^ m) • x) * (((l : w.adicCompletionIntegers E) ^ m) • x) = 0 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, hxx, smul_zero, smul_zero]
    let h₀ : GL (Fin a) (w.adicCompletionIntegers E) :=
      ⟨1 + ((l : w.adicCompletionIntegers E) ^ m) • x, 1 - ((l : w.adicCompletionIntegers E) ^ m) • x,
        by rw [add_mul, one_mul, mul_sub, mul_one, hyy, sub_zero, sub_add_cancel],
        by rw [sub_mul, one_mul, mul_add, mul_one, hyy, add_zero, add_sub_cancel_right]⟩
    have hh₀ : h₀ ∈ K₀ := (mem_ker_map_mk_iff _ h₀).2 fun i j => by
      show (1 + ((l : w.adicCompletionIntegers E) ^ m) • x) i j - (1 : Matrix (Fin a) (Fin a) _) i j ∈ _
      rw [Matrix.add_apply, add_sub_cancel_left, Matrix.smul_apply, smul_eq_mul]
      exact Ideal.mem_span_singleton'.2 ⟨x i j, mul_comm _ _⟩
    refine ⟨e ⟨h₀, hh₀⟩, ?_, ?_⟩
    · let p : Fin a → w.adicCompletion E := fun i => algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)
        (((l : w.adicCompletionIntegers E) ^ m) * ((hu.unit⁻¹ : (w.adicCompletionIntegers E)ˣ) : w.adicCompletionIntegers E) * wv i)
      let q : Fin a → w.adicCompletion E := fun j => algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E) (f j)
      have hhK : (((e ⟨h₀, hh₀⟩ : K₀.map ι) : GL (Fin a) (w.adicCompletion E)) : Matrix (Fin a) (Fin a) _) =
          1 + vecMulVec p q := by
        rw [Subgroup.coe_equivMapOfInjective_apply]
        refine Matrix.ext fun i j => ?_
        rw [GeneralLinearGroup.map_apply]
        show algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E) ((1 + ((l : w.adicCompletionIntegers E) ^ m) • x) i j) = _
        by_cases hij : i = j <;> simp [hij, x, p, q, vecMulVec_apply, Matrix.one_apply] <;> ring
      have hconj : (((g * (e ⟨h₀, hh₀⟩ : K₀.map ι) * g⁻¹ : GL (Fin a) (w.adicCompletion E))) :
          Matrix (Fin a) (Fin a) _) - 1 =
          (g : Matrix (Fin a) (Fin a) _) * vecMulVec p q * ((g⁻¹ : GL _ _) : Matrix _ _ _) := by
        rw [Units.val_mul, Units.val_mul, hhK, mul_add, mul_one, add_mul, hgg, add_sub_cancel_left]
      have hp : (g : Matrix (Fin a) (Fin a) (w.adicCompletion E)) *ᵥ p ∈ W := by
        have : p = (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)
            (((l : w.adicCompletionIntegers E) ^ m) * ((hu.unit⁻¹ : (w.adicCompletionIntegers E)ˣ) : w.adicCompletionIntegers E))) •
            (fun i => algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E) (wv i)) := by
          ext i; simp [p]
        rw [this, Matrix.mulVec_smul]
        exact W.smul_mem _ ((hmem _).1 hw)
      obtain ⟨h1, h2⟩ := conj_vecMulVec W _ _ hgg p q hp fun y hy => hf y ((hmem y).2 hy)
      exact hWcrit _ (fun v => by rw [hconj]; exact h1 v) (fun v hv => by rw [hconj]; exact h2 v hv)
    · have htr : (B * x).trace = 1 := by
        rw [Matrix.mul_smul, Matrix.trace_smul, mul_vecMulVec, trace_vecMulVec, smul_eq_mul,
          dotProduct_comm (B *ᵥ wv) f]
        exact hu.val_inv_mul
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
        hlam₀ ⟨h₀, hh₀⟩ x rfl, powChar_apply, toAdd_ofAdd, htr, hφ1, ZMod.val_one, pow_one]
      exact hζ1

end GlobalTheory.CuspType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnramifiedLocalPairOfInertWeilDatum
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertLoc

open GlobalTheory.SplitScalar GlobalTheory.FinWeilO


set_option maxHeartbeats 800000 in
theorem exists_locPair : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E), IsWeilDatumO ψ S T χS χT om → conjPl P = P → VacFix ψ om P → ∀ e, IsPrimeIdem P e e → ∃ (ϖ : P.adicCompletion D.host.E) (σ : P.adicCompletion D.host.E →+* P.adicCompletion D.host.E) (q : ℕ) (δ : P.adicCompletion D.host.E) (JS : GL (Fin S.rank) (P.adicCompletion D.host.E)) (JT : GL (Fin T.rank) (P.adicCompletion D.host.E)) (ψ' : AddChar (P.adicCompletion D.host.E) ℂ) (M : Submodule ℂ (WO S T → ℂ)) (ρ : Matrix (Fin T.rank) (Fin S.rank) (P.adicCompletion D.host.E) → Module.End ℂ M) (ω : Formalism.UG.UJ σ (JS : Matrix (Fin S.rank) (Fin S.rank) (P.adicCompletion D.host.E)) × Formalism.UG.UJ σ (JT : Matrix (Fin T.rank) (Fin T.rank) (P.adicCompletion D.host.E)) →* Module.End ℂ M) (ιS : Formalism.UG.UJ σ (JS : Matrix (Fin S.rank) (Fin S.rank) (P.adicCompletion D.host.E)) →* GA D S) (ιT : Formalism.UG.UJ σ (JT : Matrix (Fin T.rank) (Fin T.rank) (P.adicCompletion D.host.E)) →* GA D T), LocPair ϖ σ q δ JS JT ψ' ρ ω ∧ (∀ g, g ∈ ιS.range ↔ SuppF S e g) ∧ (∀ g, g ∈ ιT.range ↔ SuppF T e g) ∧ (∀ g, ιS g ∈ hyp S P ↔ (g : GL (Fin S.rank) (P.adicCompletion D.host.E)) ∈ Formalism.UG.GLint (Fin S.rank) (Formalism.UG.intL _)) ∧ (∀ g, ιT g ∈ hyp T P ↔ (g : GL (Fin T.rank) (P.adicCompletion D.host.E)) ∈ Formalism.UG.GLint (Fin T.rank) (Formalism.UG.intL _)) ∧ (∀ g h (m : M), ((ω (g, h) m : M) : WO S T → ℂ) = om (ιS g, ιT h) m) ∧ (∀ f, IsVacAt ψ S T P f → f ∈ M) ∧ ∀ m : M, LocVac ρ m ↔ IsVacAt ψ S T P m := by
  intro D ψ S T χS χT om P hW hP hfix e he
  obtain ⟨ϖ, σ, q, π, hU, h2, h, hV⟩ := exists_chart hP he
  obtain ⟨βS, ιS, hS, gS⟩ := hV S
  obtain ⟨βT, ιT, hT, gT⟩ := hV T
  obtain ⟨c, hc⟩ := exists_isGen D P
  have hψ := hW.std
  obtain ⟨δ, ψ', hδ, p1, p2, p3⟩ := exists_delta_psi hU h2 (th ψ h c) (th_conj h hU.1) (by
    obtain ⟨β, -, hβ, -⟩ := hV D.sp.X'
    refine th_cond hψ h hU.2.1 hβ ⟨0, ?_⟩ hc
    have h1 := D.R.m_add_three_le_k
    rw [D.sp.X'_rank, Ranks.rankX', Ranks.r]
    omega)
  let ρ : Matrix (Fin T.rank) (Fin S.rank) (LP D P) → Module.End ℂ (thetaSub ψ S T) := fun x =>
    (heisL ψ S T (kap h βS βT c x)).restrict fun _ hf =>
      GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (h.half_fin (kap_half h x)) hf
  have hρ : ∀ x (m : thetaSub ψ S T), (ρ x m : WO S T → ℂ) = heisO ψ S T (kap h βS βT c x) m := fun _ _ => rfl
  let ω : Formalism.UG.UJ σ (1 : Matrix (Fin S.rank) (Fin S.rank) (LP D P)) ×
      Formalism.UG.UJ σ (1 : Matrix (Fin T.rank) (Fin T.rank) (LP D P)) →* Module.End ℂ (thetaSub ψ S T) :=
    { toFun := fun p => (om (ιS p.1, ιT p.2)).restrict fun _ hf => hW.om_pres _ _ hf
      map_one' := LinearMap.ext fun m => Subtype.ext (by
        show om (ιS 1, ιT 1) m = m
        rw [map_one, map_one, Prod.mk_one_one, map_one, Module.End.one_apply])
      map_mul' := fun p p' => LinearMap.ext fun m => Subtype.ext (by
        show om (ιS (p.1 * p'.1), ιT (p.2 * p'.2)) m = om (ιS p.1, ιT p.2) (om (ιS p'.1, ιT p'.2) m)
        rw [map_mul, map_mul, ← Prod.mk_mul_mk, map_mul, Module.End.mul_apply]) }
  have hω : ∀ g k (m : thetaSub ψ S T), (ω (g, k) m : WO S T → ℂ) = om (ιS g, ιT k) m := fun _ _ _ => rfl
  have hlat := kap_mem_iff h hU.2.1 hS hT hc
  have hvac0 : ∀ m : thetaSub ψ S T, LocVac ρ m ↔
      ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), IsHalf e u → heisO ψ S T u m = m := fun m => by
    refine ⟨fun hm u hu hh => ?_, fun hm x hx => Subtype.ext (hm _ ((hlat x).2 hx) (kap_half h x))⟩
    obtain ⟨x, rfl⟩ := kap_surj (βS := βS) (βT := βT) h hc.1 hh
    exact congrArg Subtype.val (hm x ((hlat x).1 hu))
  have hvac : ∀ m : thetaSub ψ S T, LocVac ρ m ↔ IsVacAt ψ S T P m := fun m => by
    rw [hvac0]
    refine ⟨fun hm => ⟨m.2, fun e' f' he' u hu hh => hm u hu ?_⟩, fun hm u hu hh => hm.2 e e he u hu (Or.inl hh)⟩
    obtain ⟨rfl, -⟩ := ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents S).2.2.1 P e e he).2.2.2.1 e' f' he'
    rwa [h.1.2.1, or_self] at hh
  have hhyp : ∀ {V : HSp D} {β ι}, GrpChart V e σ π β ι → ∀ g, ι g ∈ hyp V P ↔
      g.1 ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.intL (LP D P)) := fun hι g =>
    ⟨fun hg => (hι.2.2.2 g).1 hg.1, fun hg => ⟨(hι.2.2.2 g).2 hg, e, e, he, hι.1 g⟩⟩
  have hone : ∀ (n : ℕ) (i j : Fin n), σ ((1 : Matrix (Fin n) (Fin n) (LP D P)) i j) = (1 : Matrix (Fin n) (Fin n) (LP D P)) j i :=
    fun n i j => by
      rw [Matrix.one_apply, Matrix.one_apply]
      by_cases hij : i = j
      · rw [if_pos hij, if_pos hij.symm, σ.map_one]
      · rw [if_neg hij, if_neg (Ne.symm hij), σ.map_zero]
  refine ⟨ϖ, σ, q, δ, 1, 1, ψ', thetaSub ψ S T, ρ, ω, ιS, ιT,
    ⟨hU, odd_of_v_two hU h2, one_mem _, one_mem _, hone _, hone _, hδ, p1, p2, ?_, fun x y => ?_, ?_, fun g k x => ?_,
      fun g k hg hk s hs => ?_⟩,
    fun g => ⟨?_, gS.2.2.1 g⟩, fun g => ⟨?_, gT.2.2.1 g⟩, hhyp gS, hhyp gT, hω, fun f hf => hf.1, hvac⟩
  · refine LinearMap.ext fun m => Subtype.ext ?_
    rw [hρ, kap_zero, heisO_zero, Module.End.one_apply]
  · refine LinearMap.ext fun m => Subtype.ext ?_
    rw [Module.End.mul_apply, hρ, hρ, heisO_heisO, symplOH_kap h hS hT, LinearMap.smul_apply, Submodule.coe_smul, hρ, kap_add,
      locH, p3, inv_one, Units.val_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
    rfl
  · refine span_vacua hψ h.1.1 h.1.2.1 (fun u hu hh => ?_) _ fun u hh s m hs hm => ?_
    · obtain ⟨x, rfl⟩ := kap_surj (βS := βS) (βT := βT) h hc.1 hh
      refine ⟨kap h βS βT c ((2⁻¹ : LP D P) • x), (hlat _).2 fun i j => mul_mem (mem_intL.2 ?_) ((hlat x).1 hu i j), ?_⟩
      · rw [map_inv₀, h2, inv_one]
      · rw [← kap_add, half_add_half]
    · obtain ⟨x, rfl⟩ := kap_surj (βS := βS) (βT := βT) h hc.1 hh
      exact Submodule.subset_span ⟨x, s, (hvac0 s).2 hs, Subtype.ext hm⟩
  · refine LinearMap.ext fun m => Subtype.ext ?_
    show om (ιS g, ιT k) (heisO ψ S T (kap h βS βT c x) m) = heisO ψ S T (kap h βS βT c _) (om (ιS g, ιT k) m)
    rw [hW.om_heis _ _ _ _ m.2, actO_kap h gS gT]
  · exact Subtype.ext (hfix _ ((hvac s).1 hs) _ ((hhyp gS g).2 hg) _ ((hhyp gT k).2 hk))
  · rintro ⟨g, rfl⟩; exact gS.1 g
  · rintro ⟨g, rfl⟩; exact gT.1 g

end GlobalTheory.InertLoc
end
end

