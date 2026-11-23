module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0573
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0556
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0497
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0045
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SchwartzBruhatEqSumPure
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0038
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0024
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0049
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolume
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0018
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalSectionLogNormOnSheet
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

theorem log_eq_of_frame {a ρ F G Pa Pb φ h : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hF : 0 < F) (hG : 0 < G)
    (hPa : 0 < Pa) (hPb : 0 < Pb) (hh : h = Pa / Pb * a * Real.exp (φ / 2))
    (e : a * ρ * (G / Pb) = F / Pa) : Real.log ρ - φ / 2 = Real.log (F / G / h) := by
  have hE := Real.exp_pos (φ / 2)
  have key : F / G / h = ρ / Real.exp (φ / 2) := by
    have hF' : F = a * ρ * (G / Pb) * Pa := by
      rw [e]
      field_simp
    rw [hh, hF']
    field_simp
  rw [key, Real.log_div hρ.ne' hE.ne', Real.log_exp]

theorem value_of_ne_zero : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : GlobalTheory.HermLB (mpStr ℤ m n)) (A : HermLine (Bk n)) (X : Scheme.{0}) [IsIntegral X]
    (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (r : (M.restr i).B.ι → X.functionFieldˣ) (hr : IsRatSec (M.restr i).B r)
    (f g : Pol n), IsRatSectionOn (ptIdeal (i (genericPoint X))) A f g → RatOf M A r f g →
    ∀ (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ), GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z →
      eval z (map (Int.castRingHom ℂ) f) ≠ 0 → eval z (map (Int.castRingHom ℂ) g) ≠ 0 →
      y ∈ offSupp (i ≫ mpStr ℤ m n) σ₀ ((M.restr i).div hr) ∧
      GlobalTheory.Cartier.logNorm ((M.restr i).φ σ₀) r y = logNormRat A f g z := by
  intro m n M A X _ i _ r hr f g hfg hrat y z hz hf0 hg0
  obtain ⟨α, β, hf, hg, -, -, hdeg⟩ := hfg
  obtain ⟨u, hu, hcl⟩ := hrat
  obtain ⟨w, hw⟩ : ∃ w, w = PtsOver.map i rfl _ y := ⟨_, rfl⟩
  have hz' : IsUnder w z := hw ▸ hz
  have hwb := mem_pick (M.φ σ₀).isLB w
  obtain ⟨b, hb⟩ : ∃ b, b = pick (M.φ σ₀).isLB w := ⟨_, rfl⟩
  rw [← hb] at hwb
  obtain ⟨c, hc⟩ : ∃ c : ∀ k, Bk n k, c = fun k => ptChart (w.1 (IsLocalRing.closedPoint ℂ)) k := ⟨_, rfl⟩
  have hwc : w ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) :=
    CxPts.mem_ptsIn.2 (Set.mem_iInter.2 fun k => hc ▸ mem_ptChart _ k)
  have hwbc : w ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U b ⊓ mchart c) := mem_ptsIn_inf.2 ⟨hwb, hwc⟩
  have pre : ∀ V : (MP ℤ m n).Opens, w ∈ ptsIn (mpStr ℤ m n) σ₀ V → y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ V) := by
    intro V hV
    subst hw
    exact CxPts.mem_ptsIn.2 (CxPts.mem_ptsIn.1 hV)
  have hyc := pre _ hwc
  have hybc := pre _ hwbc
  have hyb := pre _ hwb
  have hgc : genericPoint X ∈ i ⁻¹ᵁ mchart c := gen_mem (CxPts.mem_ptsIn.1 hyc)
  have hgb : genericPoint X ∈ i ⁻¹ᵁ (M.B.U b ⊓ mchart c) := gen_mem (CxPts.mem_ptsIn.1 hybc)
  have e := hcl b c hgc hgb
  have hne : ∀ a : Fin (m + 1) → ℕ, ∏ k, z ⟨k, c k⟩ ^ a k ≠ 0 := fun a =>
    Finset.prod_ne_zero_iff.2 fun k _ =>
      pow_ne_zero _ ((hz' k (c k)).1.1 (CxPts.ptsIn_mono (mchart_le c k) hwc))
  have val : ∀ (s : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog s a →
      ratVal (fnAt i c hgc s) y = eval z (map (Int.castRingHom ℂ) s) / ∏ k, z ⟨k, c k⟩ ^ a k := by
    intro s a hs
    refine (ratVal_fnOf hyc hgc _).trans ((CxPts.ev_app i rfl _ _ y).trans ?_)
    rw [← hw]
    exact ev_dehomog_of_isUnder m n c s a hs w z hz' hwc
  have unit : ∀ (s : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog s a →
      eval z (map (Int.castRingHom ℂ) s) ≠ 0 → UnitAt (under y) (fnAt i c hgc s) := by
    intro s a hs h0
    refine (unitAt_fnOf_iff (CxPts.mem_ptsIn.1 hyc) hgc _).2 (CxPts.mem_ptsIn.1 ((mem_ptsIn_basicOpen hyc _).2 ?_))
    rw [← ratVal_fnOf hyc hgc]
    change ratVal (fnAt i c hgc s) y ≠ 0
    rw [val s a hs]
    exact div_ne_zero h0 (hne a)
  have hF := unit f α hf hf0
  have hG := unit g β hg hg0
  have hU : UnitAt (under y) (fnOf _ hgb (i.app _ (u b c).val)) := by
    obtain ⟨v, hv⟩ := (u b c).isUnit.map (i.app (M.B.U b ⊓ mchart c)).hom
    have hv' : (v : Γ(X, i ⁻¹ᵁ (M.B.U b ⊓ mchart c))) = i.app _ (u b c).val := hv
    rw [← hv']
    exact unitAt_fnOf (CxPts.mem_ptsIn.1 hybc) hgb v
  have hR : UnitAt (under y) (r fun _ => b : X.functionField) := by
    have e' : (r fun _ => b : X.functionField) =
        fnAt i c hgc f * (fnOf _ hgb (i.app _ (u b c).val) * fnAt i c hgc g)⁻¹ := by
      rw [← e]
      have h1 := hU.ne_zero
      have h2 := hG.ne_zero
      field_simp
    rw [e']
    exact hF.mul (hU.mul hG).inv
  have hxb : under y ∈ (M.restr i).B.U (fun _ => b) := by
    refine Set.mem_iInter.2 fun _ => ?_
    subst hw
    exact CxPts.mem_ptsIn.1 hwb
  have hyb' : y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ ((M.restr i).B.U (fun _ => b)) := CxPts.mem_ptsIn.2 hxb
  have ho : y ∈ offSupp (i ≫ mpStr ℤ m n) σ₀ ((M.restr i).div hr) :=
    mem_offSupp.2 fun hs =>
      ((presents_divOfRatSec (M.restr i).isLB hr).isEqn (fun _ => b) _ hxb).mem_supp_iff.1 hs hR
  refine ⟨ho, ?_⟩
  have hφ : ((M.restr i).φ σ₀).φ (fun _ => b) y = (M.φ σ₀).φ b w := by
    rw [hw]
    exact GlobalTheory.Weight.pull_φ (M.φ σ₀) i rfl _ y
  have hvU : ratVal (fnOf _ hgb (i.app _ (u b c).val)) y =
      CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U b ⊓ mchart c) (u b c : Γ(MP ℤ m n, M.B.U b ⊓ mchart c)) w := by
    refine (ratVal_fnOf hybc hgb _).trans ((CxPts.ev_app i rfl _ _ y).trans ?_)
    rw [← hw]
  have ev' := congrArg (ratVal · y) e
  simp only at ev'
  rw [ratVal_mul (hU.mul hR).regAt hG.regAt, ratVal_mul hU.regAt hR.regAt, hvU, val g β hg, val f α hf] at ev'
  have hP : ∀ a : Fin (m + 1) → ℕ, 0 < ∏ k, ‖z ⟨k, c k⟩‖ ^ a k := fun a => by
    have := norm_pos_iff.2 (hne a)
    simpa only [norm_prod, norm_pow] using this
  have hh := hu.2.2 b c w z hz' hwbc
  have hzp : ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k =
      (∏ k, ‖z ⟨k, c k⟩‖ ^ α k) / ∏ k, ‖z ⟨k, c k⟩‖ ^ β k := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have h0 : ‖z ⟨k, c k⟩‖ ≠ 0 := norm_ne_zero_iff.2 ((hz' k (c k)).1.1 (CxPts.ptsIn_mono (mchart_le c k) hwc))
    rw [← hdeg k, zpow_sub₀ h0, zpow_natCast, zpow_natCast]
  rw [hzp] at hh
  rw [logNorm_eq _ hr ho hyb', hφ, logNormRat]
  have evn := congrArg norm ev'
  simp only [norm_mul, norm_div, norm_prod, norm_pow] at evn
  exact log_eq_of_frame (norm_pos_iff.2 (ev_ne_zero hwbc (u b c).isUnit)) (norm_pos_iff.2 (ratVal_ne_zero hR))
    (norm_pos_iff.2 hf0) (norm_pos_iff.2 hg0) (hP α) (hP β) hh evn

end GlobalTheory.CompanionTheory.MixZ.ArchEq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalTupleInLatticeLevel
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatMem

theorem exists_nat_mul_mem (F : Type) [Field F] [NumberField F] (x : F) :
    ∃ m : ℕ, 0 < m ∧ ∃ r : 𝓞 F, (r : F) = (m : F) * x :=
  _root_.UpperTheory.Reformulated.B.ExistsNatMulMem.exists_nat_mul_mem F x

theorem repr_inclR {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (x : E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Af F) b).repr (inclR (Af F) x) k
      = algebraMap F (Af F) (b.repr x k) := by
  have h : inclR (Af F) x = (1 : Af F) ⊗ₜ[F] x := rfl
  rw [h, Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem natCast_mul_eq_smul {F E : Type} [Field F] [Field E] [Algebra F E] (n : ℕ) (z : E) :
    (n : E) * z = (n : F) • z := by
  rw [Algebra.smul_def, map_natCast]

theorem intCast_mul_eq_smul {F E : Type} [Field F] [Field E] [Algebra F E] (n : ℤ) (z : E) :
    (n : E) * z = (n : F) • z := by
  rw [Algebra.smul_def, map_intCast]

theorem exists_clear_family {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E) {ι : Type} [Fintype ι] (e : ι → E) :
    ∃ D : ℕ, 0 < D ∧ ∀ (t : ι) (o : 𝓞 E) (k : Fin d),
      ∃ r : 𝓞 F, (r : F) = b.repr ((D : E) * (e t * (o : E))) k := by
  classical
  let B := RingOfIntegers.basis E
  choose m hm hr using fun p : ι × Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin d =>
    exists_nat_mul_mem F (b.repr (e p.1 * (B p.2.1 : E)) p.2.2)
  refine ⟨∏ p, m p, Finset.prod_pos fun p _ => hm p, fun t o k => ?_⟩
  set D : ℕ := ∏ p, m p with hDdef
  have hterm : ∀ l, ∃ r : 𝓞 F, (r : F) = b.repr ((D : E) * (e t * (B l : E))) k := by
    intro l
    obtain ⟨c, hc⟩ : m (t, l, k) ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
    obtain ⟨r, hr1⟩ := hr (t, l, k)
    refine ⟨(c : 𝓞 F) * r, ?_⟩
    rw [natCast_mul_eq_smul (F := F), map_smul, Finsupp.smul_apply, smul_eq_mul, hc]
    simp only [map_mul, map_natCast, Nat.cast_mul]
    have hr2 : (r : F) = (m (t, l, k) : F) * b.repr (e t * (B l : E)) k := hr1
    change (c : F) * (r : F) = _
    rw [hr2]
    ring
  choose r hr' using hterm
  refine ⟨∑ l, (B.repr o l) • r l, ?_⟩
  have ho : (o : E) = ∑ l, ((B.repr o l : ℤ) : E) * (B l : E) := by
    have h3 := congrArg (algebraMap (𝓞 E) E) (B.sum_repr o)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h3
    rw [show (o : E) = algebraMap (𝓞 E) E o from rfl, ← h3]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [zsmul_eq_mul]
  have hsum : (D : E) * (e t * (o : E))
      = ∑ l, ((B.repr o l : ℤ) : F) • ((D : E) * (e t * (B l : E))) := by
    rw [ho, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← intCast_mul_eq_smul]
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum, Finsupp.finsetSum_apply]
  have h4 : ((∑ l, (B.repr o l) • r l : 𝓞 F) : F) = ∑ l, ((B.repr o l : ℤ) : F) * (r l : F) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show ((∑ l, (B.repr o l) • r l : 𝓞 F) : F)
      = algebraMap (𝓞 F) F (∑ l, (B.repr o l) • r l) from rfl, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [zsmul_eq_mul]
  rw [h4]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hr']

theorem ratTuple_mem_latN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n N : ℕ), 0 < N →
    ∃ s : ℕ, 0 < s ∧ ∀ ρ : Fin M → Fin n → 𝓞 E, ratTuple J s ρ ∈ latN b n M N := by
  intro F E _ _ _ _ _ d b M J n N hN
  obtain ⟨D, hD0, hD⟩ := exists_clear_family b (fun p : Fin M × Fin M => J⁻¹ p.1 p.2)
  refine ⟨N * D, Nat.mul_pos hN hD0, fun ρ => ?_⟩
  show ∀ a i, InNOh b N (ratTuple J (N * D) ρ a i)
  intro a j k
  choose r hr using fun i => hD (j, i) (ρ i a) k
  refine ⟨algebraMap F (Af F) (((∑ i, r i : 𝓞 F)) : F), ?_, ?_⟩
  · exact ((_root_.GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology F).2.2.2.2.2.2.1 _).2 ⟨_, rfl⟩
  · show (Algebra.TensorProduct.basis (Af F) b).repr
      (inclR (Af F) (((N * D : ℕ) : E) *
        (J⁻¹ *ᵥ fun i => algebraMap (𝓞 E) E (ρ i a)) j)) k = _
    rw [repr_inclR]
    have h1 : ((N * D : ℕ) : E) * (J⁻¹ *ᵥ fun i => algebraMap (𝓞 E) E (ρ i a)) j
        = (N : F) • ∑ i, (D : E) * (J⁻¹ j i * (ρ i a : E)) := by
      rw [← natCast_mul_eq_smul, Nat.cast_mul, Matrix.mulVec, dotProduct, ← Finset.mul_sum,
        mul_assoc]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, map_smul, Finsupp.smul_apply, smul_eq_mul, map_sum, Finsupp.finsetSum_apply,
      map_mul, map_natCast]
    congr 2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show ((∑ i, r i : 𝓞 F) : F) = algebraMap (𝓞 F) F (∑ i, r i) from rfl, map_sum]
    exact Finset.sum_congr rfl fun i _ => (hr i).symm

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatMem
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepJacquetWordMultiplicity
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.FineL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem length_decWord (Γ : Segment k) : (decWord Γ).length = Γ.len := by
  simp [decWord]

theorem decWord_get (Γ : Segment k) (a : Fin (decWord Γ).length) :
    (decWord Γ).get a = Γ.first.nu ((Γ.len - 1 - (a : ℕ) : ℕ) : ℂ) := by
  have h : (a : ℕ) < (List.ofFn Γ.term).reverse.length := a.2
  show (List.ofFn Γ.term).reverse[(a : ℕ)] = _
  rw [List.getElem_reverse, List.getElem_ofFn]
  simp [Segment.term]

theorem isCusp_decWord_get (Γ : Segment k) (a : Fin (decWord Γ).length) : ((decWord Γ).get a).IsCusp := by
  rw [decWord_get]
  exact Γ.isCusp_first.nu _

theorem sum_decWord (Γ : Segment k) : ∑ a, ((decWord Γ).get a).1 = Γ.deg := by
  have h : ∀ a, ((decWord Γ).get a).1 = Γ.d := fun a => by rw [decWord_get]; rfl
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, length_decWord]
  rfl

theorem below_of_len_one {s : ℕ} (Γ : Fin s → Segment k) (h : ∀ a, (Γ a).len = 1) (a : Fin s) :
    below Γ a = s - 1 - (a : ℕ) := by
  simp only [below, h, Finset.sum_const, smul_eq_mul, mul_one]
  rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]

theorem jmL_decWord (hJ : LSegJacquet k) (Γ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (hΓ : IsLSeg Γ π) : jmL (decWord Γ) π = 1 := by
  have hd : ∑ a, ((decWord Γ).get a).1 = N := (sum_decWord Γ).trans hΓ.deg_eq
  rw [jmL, dite_eq_left hd]
  refine (hJ Γ π hΓ _ (decWord Γ).get hd fun a => (isCusp_decWord_get Γ a).1).1
    ⟨fun a => Segment.single _ (isCusp_decWord_get Γ a), ⟨?_, fun a => ?_⟩,
      fun a => (single_spec (isCusp_decWord_get Γ a)).2.1⟩
  · have h : ∀ a, (Segment.single _ (isCusp_decWord_get Γ a)).len = 1 := fun _ => rfl
    simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, length_decWord]
  · refine (decWord_get Γ a).trans ?_
    have e : (decWord Γ).length - 1 - (a : ℕ) = Γ.len - 1 - (a : ℕ) := by
      have := length_decWord Γ
      omega
    rw [below_of_len_one _ (fun _ => rfl), e]

theorem len_eq_one (hJ : LSegJacquet k) {Δ : Segment k} {x : IrrGL (k := k)} (hx : x.IsCusp) (h : IsLSeg Δ x.rep) :
    Δ.len = 1 := by
  have hd : ∑ a, ((decWord Δ).get a).1 = x.1 := (sum_decWord Δ).trans h.deg_eq
  have h1 := jmL_decWord hJ Δ h
  rw [jmL, dite_eq_left hd, jm] at h1
  have hsub : IsSubquotient (piTensor fun a => ((decWord Δ).get a).rep)
      (GlobalTheory.SmGL.jac (stdBlocks (fun a => ((decWord Δ).get a).1) hd) x.rep) :=
    jhMult_ne_zero_iff.1 (by rw [h1]; exact one_ne_zero)
  have hu := GlobalTheory.SmGL.CuspRow.block_unique_of_isCuspidal k x.1 _ x.rep _ _ _ _
    (fun a => ((decWord Δ).get a).rep) hx.2 (fun a => nontrivial_of_irreducible ((decWord Δ).get a).2.rep.irr) hsub
  by_contra hne
  have hl : 2 ≤ (decWord Δ).length := by
    have := Δ.len_pos
    rw [length_decWord]
    omega
  have := hu ⟨0, by omega⟩ ⟨1, by omega⟩ (isCusp_decWord_get Δ _).1 (isCusp_decWord_get Δ _).1
  simp at this

theorem eq_of_isLSeg_single {ρ : IrrGL (k := k)} (hρ : ρ.IsCusp) {x : IrrGL (k := k)} (h : IsLSeg (.single ρ hρ) x.rep) : x = ρ := by
  have hdeg : ρ.1 = x.1 := by
    have := h.deg_eq
    simpa [Segment.deg, Segment.single, Segment.ofFirst] using this
  obtain ⟨n, c⟩ := x
  obtain ⟨m, r⟩ := ρ
  obtain rfl : m = n := hdeg
  obtain ⟨φ⟩ := (single_spec hρ).2.1.unique h
  exact (IrrGL.of_rep _).symm.trans ((IrrGL.of_eq_of.2 ⟨φ⟩).trans (IrrGL.of_rep _))

theorem eq_first_of_len_one {Δ : Segment k} (hl : Δ.len = 1) {x : IrrGL (k := k)} (h : IsLSeg Δ x.rep) : x = Δ.first := by
  have e : Δ = .single Δ.first Δ.isCusp_first := Segment.ext_first rfl hl
  exact eq_of_isLSeg_single Δ.isCusp_first (e ▸ h)

theorem jmL_cusp_word : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → LSegJacquet k → ∀ (Γ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsLSeg Γ π → ∀ W : List (IrrGL (k := k)), (∀ w ∈ W, w.IsCusp) →
    (W = decWord Γ → jmL W π = 1) ∧ (W ≠ decWord Γ → jmL W π = 0) := by
  intro k _ _ _ _ _ hJ Γ N V _ _ π hΓ W hW
  refine ⟨fun e => e ▸ jmL_decWord hJ Γ hΓ, fun hne => ?_⟩
  by_cases hd : ∑ a, (W.get a).1 = N
  · rw [jmL, dite_eq_left hd]
    refine (hJ Γ π hΓ _ W.get hd fun a => (hW _ (List.get_mem W a)).1).2 ?_
    rintro ⟨Γ', ⟨hs, hf⟩, hL⟩
    have hl : ∀ a, (Γ' a).len = 1 := fun a => len_eq_one hJ (hW _ (List.get_mem W a)) (hL a)
    have hlen : W.length = Γ.len := by
      simpa only [hl, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using hs
    refine hne (List.ext_get (hlen.trans (length_decWord Γ).symm) fun n h1 h2 => ?_)
    have h3 : W.get ⟨n, h1⟩ = Γ.first.nu ((W.length - 1 - n : ℕ) : ℂ) := by
      have h4 := eq_first_of_len_one (hl ⟨n, h1⟩) (hL ⟨n, h1⟩)
      rw [hf, below_of_len_one Γ' hl] at h4
      exact h4
    rw [h3, decWord_get, hlen]
  · rw [jmL, dite_eq_right hd]

end GlobalTheory.CompanionTheory.FineL

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheetDensityLogNormFormula
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

section Torus

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem eval_torus_of_homog {s : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a) (c : K → ℂ)
    (u : (Σ k, ι k) → ℂ) :
    eval (fun p => c p.1 * u p) (map (Int.castRingHom ℂ) s) =
      (∏ k, c k ^ a k) * eval u (map (Int.castRingHom ℂ) s) := by
  rw [MvPolynomial.eval_map, MvPolynomial.eval_map, MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hprod : ∏ p, (c p.1 * u p) ^ d p = (∏ k, c k ^ a k) * ∏ p, u p ^ d p := by
    simp only [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ d ⟨k, i⟩ = c k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hs d hd k]
  rw [hprod]
  ring

private theorem ratio_cancel {a b F G H : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * F / (b * G) / (a / b * H) = F / G / H := by
  by_cases hG : G = 0
  · simp [hG]
  by_cases hH : H = 0
  · simp [hH]
  field_simp

theorem logNormRat_torus {P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)} {A : HermLine ι} {f g : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι}
    (h : IsRatSectionOn P A f g) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    logNormRat A f g (fun p => c p.1 * z p) = logNormRat A f g z := by
  obtain ⟨α, β, hf, hg, -, -, hd⟩ := h
  have hne : ∀ (a : K → ℕ), ‖∏ k, c k ^ a k‖ ≠ 0 := fun a =>
    norm_ne_zero_iff.2 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k))
  have hab : ∏ k, ‖c k‖ ^ A.a k = ‖∏ k, c k ^ α k‖ / ‖∏ k, c k ^ β k‖ := by
    rw [norm_prod, norm_prod, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← hd k, zpow_sub₀ (norm_ne_zero_iff.2 (hc k)), norm_pow, norm_pow, zpow_natCast, zpow_natCast]
  unfold logNormRat
  rw [eval_torus_of_homog hf, eval_torus_of_homog hg, A.smul c z hc, norm_mul, norm_mul, hab,
    ratio_cancel (hne α) (hne β)]

end Torus

theorem sheetDensity_eq_of_isSheet : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (P : Ideal (Pol n)) (D : ℕ) (Ψ : GlobalTheory.CompanionTheory.MixZ.ArchEq.LinProj n D)
    (B A : HermLine (Bk n)) (f g : Pol n), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (D + 1) → IsGoodProj P Ψ → IsSmoothHerm B →
    IsRatSectionOn P A f g → ∀ᵐ v : Fin D → ℂ, ∀ w γ, IsSheet P Ψ v w γ →
      sheetDensity P Ψ (pot fun _ : Fin D => B) (logNormRat A f g) v w =
        logNormRat A f g (γ v) * maDensity (fun _ y' => Real.log (B.h (γ y'))) v := by
  intro m n P D Ψ B A f g hP hΨ hB hA
  let A' : HermLine (Bk n) := ReciprocityTheory.ChartRestriction.G.AI.I2.constLine 1
  have hA1 : ∀ z, ReciprocityTheory.ChartRestriction.G.Geo.logNorm A' 1 z = 1 := fun z => by
    simp [ReciprocityTheory.ChartRestriction.G.Geo.logNorm, A', ReciprocityTheory.ChartRestriction.G.AI.I2.constLine, HermLine.ofWeight, Real.exp_neg]
  have hAs : IsSmoothHerm A' := contDiffOn_const
  have hs : ReciprocityTheory.ChartRestriction.G.Geo.IsSectionOn P A' 1 := by
    refine ⟨0, fun k => by simp [A', ReciprocityTheory.ChartRestriction.G.AI.I2.constLine, HermLine.ofWeight], fun d hd k => ?_, fun h => ?_⟩
    · rw [MvPolynomial.support_one, Finset.mem_singleton] at hd
      subst hd
      simp
    · exact hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  filter_upwards [ReciprocityTheory.ChartRestriction.G.Geo.sheetIndep (Fin (m + 1)) (Bk n) P D Ψ (fun _ => B) A' 1 hP hΨ (fun _ => hB) hAs hs]
    with v hind w γ hγ
  have hex : ∃ γ, IsSheet P Ψ v w γ := ⟨γ, hγ⟩
  have hc := hex.choose_spec
  have h1 := hind w _ γ hc hγ
  simp only [hA1, one_mul] at h1
  have hval : logNormRat A f g (hex.choose v) = logNormRat A f g (γ v) := by
    obtain ⟨c, hcne, hcz⟩ := ReciprocityTheory.ChartRestriction.G.Geo.sameOrbit_of_segre hγ.2.self_of_nhds.2.1.1 1 one_ne_zero
      (by rw [one_smul, hc.1, hγ.1])
    rw [hcz]
    exact logNormRat_torus hA hcne _
  unfold sheetDensity
  rw [dite_eq_left hex, hval]
  exact congrArg (logNormRat A f g (γ v) * ·) h1

end GlobalTheory.CompanionTheory.MixZ.ArchEq
end
end

