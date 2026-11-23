module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0077
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0215
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0190
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0187
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationCompleteDVR
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0172
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsTorsMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.FlatTors.TorsMapExists

open ReciprocityTheory.ChartRestriction.G.DVR

theorem isPull_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' T'' : Over (Sp R)}
    {a : T'.left ⟶ T.left} {b : T''.left ⟶ T'.left} {g : GtPt D T} {g' : GtPt D T'} {g'' : GtPt D T''}
    (h : GtPt.IsPull a g g') (h' : GtPt.IsPull b g' g'') : GtPt.IsPull (b ≫ a) g g'' := by
  refine ⟨by rw [h'.1, h.1, Category.assoc], fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  rw [val_corr hJ (h'.2 χ), val_pull hJ, val_corr hJ (h.2 χ), val_pull hJ, val_pull hJ]
  simp only [Category.assoc]

theorem isPullF_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' : Over (Sp R)}
    {F : Type} [Field F] [Algebra (FractionRing R) F]
    {a : T'.left ⟶ T.left} {b : Sp F ⟶ T'.left} {g : GtPt D T} {g' : GtPt D T'} {g'' : GtPtF D F}
    (h : GtPt.IsPull a g g') (h' : GtPt.IsPullF F b g' g'') : GtPt.IsPullF F (b ≫ a) g g'' :=
  isPull_trans (T'' := TF (R := R) F) (g'' := ⟨g''.b, g''.s, g''.isGen, g''.s_zero, g''.mult⟩) h h'

end GlobalTheory.FlatTors.TorsMapExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelFamilySRep
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.SiegelLargeLevel

theorem isAlgebraic_of_mem_ZP {p M : ℕ} (hM : M ≠ 0) {x : ℂ} (hx : x ∈ ZP p M) : IsAlgebraic ℤ x := by
  rw [IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ, ← mem_algebraicClosure_iff]
  have hle : ZP p M ≤ (algebraicClosure ℚ ℂ).toSubalgebra.toSubring := by
    refine Subring.closure_le.2 ?_
    rintro y (rfl | ⟨n, -, rfl⟩)
    · have h1 : zeta M ^ M = 1 := (Complex.isPrimitiveRoot_exp M hM).pow_eq_one
      exact mem_algebraicClosure_iff.2
        (IsAlgebraic.of_pow (Nat.pos_of_ne_zero hM) (h1 ▸ isAlgebraic_one))
    · exact (algebraicClosure ℚ ℂ).inv_mem (natCast_mem _ n)
  exact hle hx

theorem exists_siegelFamily_sRep : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (h n : ℕ), 1 ≤ h → n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ p : ℕ, p.Prime → n ≠ p → ∃ Ag : SiegelFamily h p ((n ^ j) ^ 2), SRep Ag := by
  intro L L2 hθ hU h n hh hn hodd
  obtain ⟨j₀, hj₀⟩ := _root_.GlobalTheory.ZM.SiegelArithFamily.nonempty_sFam L L2 hθ hU h n hh hn hodd
  refine ⟨max j₀ 1, fun j hj p hp hnp => ?_⟩
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  obtain ⟨o, _, b, em, i, hem, hζ, hi, hconst⟩ :=
    GlobalTheory.ZM.CycBase.exists_base n (j * 2) p ((n ^ j) ^ 2) hn hp hnp (by omega) (pow_mul n j 2).symm
  obtain ⟨F⟩ := hj₀ j (le_trans (le_max_left _ _) hj) o b em hem
  have h3 : 3 ≤ n := by
    have := hn.two_le
    rcases hodd with ⟨m, rfl⟩
    omega
  have hk : 3 ≤ (n ^ j) ^ 2 := by
    rw [← pow_mul]
    exact h3.trans (Nat.le_self_pow (by omega) n)
  have hinj : Function.Injective i := fun x y hxy => hem.2.2 (by rw [← hi, ← hi, hxy])
  have halg : Algebra.IsAlgebraic ℤ o := ⟨fun x => by
    have hx : IsAlgebraic ℤ (em.toIntAlgHom x) := by
      change IsAlgebraic ℤ (em x)
      rw [← hi]
      exact isAlgebraic_of_mem_ZP (by omega) (i x).2
    exact (isAlgebraic_algHom_iff em.toIntAlgHom hem.2.2).1 hx⟩
  exact _root_.GlobalTheory.SiegelFamilyBaseChange.exists_siegelFamily L L2 h _ p o _ i (hodd.pow.pow) hk hp hinj hζ hconst halg F

end GlobalTheory.ZM.SiegelLargeLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFamilyPelSmoothGenericFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaFamily_pel_smooth_generic_fibre : Out.Laws → Out.Laws2 → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (ρ : o), em ρ = H.rt0 → ArBase em → ∃ (F : ThetaFam n em (PELClass (b := b) D a bas ρ em)) (τ : SAB H F.MM), IsPEL D a bas ρ F.univ τ ∧ SmoothOfRelativeDimension D.dim (pullback.snd F.s (spMap (algebraMap o (FractionRing o)))) := by
  first | exact @GlobalTheory.ZM.exists_thetaFam_isPEL_smooth | exact GlobalTheory.ZM.exists_thetaFam_isPEL_smooth | (intros; apply GlobalTheory.ZM.exists_thetaFam_isPEL_smooth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniversalQuasiProjectiveSiegelFamilyLargeL
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.ZM.SiegelUniversal

theorem isAlgebraic_of_injective {p M : ℕ} (hM : M ≠ 0) {o : Type} [CommRing o] (i : o →+* ZP p M)
    (hi : Function.Injective i) : Algebra.IsAlgebraic ℤ o := by
  have hle : ZP p M ≤ (algebraicClosure ℚ ℂ).toSubalgebra.toSubring := by
    refine Subring.closure_le.2 ?_
    rintro y (rfl | ⟨n, -, rfl⟩)
    · have h1 : zeta M ^ M = 1 := (Complex.isPrimitiveRoot_exp M hM).pow_eq_one
      exact mem_algebraicClosure_iff.2
        (IsAlgebraic.of_pow (Nat.pos_of_ne_zero hM) (h1 ▸ isAlgebraic_one))
    · exact (algebraicClosure ℚ ℂ).inv_mem (natCast_mem _ n)
  refine ⟨fun x => ?_⟩
  rw [← isAlgebraic_algHom_iff ((ZP p M).subtype.comp i).toIntAlgHom (Subtype.val_injective.comp hi),
    IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ, ← mem_algebraicClosure_iff]
  exact hle (i x).2

theorem exists_siegelFamily_siegRep : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ h n : ℕ, 1 ≤ h → n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ p : ℕ, p.Prime → p ≠ n → ∃ Ag : SiegelFamily h p ((n ^ j) ^ 2), SiegRep Ag := by
  intro L L2 hθ hU h n hh hn hodd
  obtain ⟨j₀, hj₀⟩ := _root_.GlobalTheory.ZM.SiegelArithFamily.nonempty_sFam L L2 hθ hU h n hh hn hodd
  refine ⟨max j₀ 1, fun j hj p hp hnp => ?_⟩
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  obtain ⟨o, _, b, em, i, hem, hζ, hi, hconst⟩ :=
    GlobalTheory.ZM.CycBase.exists_base n (j * 2) p ((n ^ j) ^ 2) hn hp hnp.symm (by omega) (pow_mul n j 2).symm
  obtain ⟨F⟩ := hj₀ j (le_trans (le_max_left _ _) hj) o b em hem
  have h3 : 3 ≤ n := by
    have := hn.two_le
    rcases hodd with ⟨m, rfl⟩
    omega
  have hk : 3 ≤ (n ^ j) ^ 2 := by
    rw [← pow_mul]
    exact h3.trans (Nat.le_self_pow (by omega) n)
  have hinj : Function.Injective i := fun x y hxy => hem.2.2 (by rw [← hi, ← hi, hxy])
  obtain ⟨Ag, hAg⟩ := _root_.GlobalTheory.SiegelFamilyBaseChange.exists_siegelFamily L L2 h _ p o _ i (hodd.pow.pow) hk hp hinj hζ hconst
    (isAlgebraic_of_injective (by omega) i hinj) F
  obtain ⟨F', -⟩ := F.exists_baseChange i hinj hζ
  obtain ⟨Ag', -, H⟩ := F'.exists_sRep_siegRep (by omega) Ag hAg
  exact ⟨Ag', H⟩

end GlobalTheory.ZM.SiegelUniversal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeNonemptyAtEveryLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem moduli_nonempty_all_levels : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → N1ab := by
  intro h1 h2 h3 h4 E _ _ _ H D l hD
  obtain ⟨n, hn, hodd, hl⟩ := _root_.GlobalTheory.ZM.exists_prime_level E H l
  obtain ⟨j, hj⟩ := _root_.GlobalTheory.ZM.exists_moduli_prime_power_level h1 h2 h3 h4 E H D n hD hn hodd
  obtain ⟨l₀, l₂, hM, hA, h02, h2'⟩ := hl ((n ^ j) ^ 2) (pow_pos (pow_pos hn.pos j) 2)
  exact _root_.GlobalTheory.ZM.moduli_of_deeper_level h1 h2 h3 E H D l l₂ hD h2'
    (_root_.GlobalTheory.nonempty_moduli_of_dvd h1 h2 E H D l₀ l₂ hD h02 (hj l₀ hM hA))

end GlobalTheory.ZM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyHeckeCorrespondenceScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem corr_kerSet_unique {S : Scheme.{0}} {G G' : Over S} [GrpObj G'] {ψ : G ⟶ G'} {K K' : Set G.left}
    (h : KerSet ψ K) (h' : KerSet ψ K') : K = K' := by
  ext g
  obtain ⟨k, _, _, z₀, hz⟩ := exists_geomPt_range_eq G.left g
  let z : Over.mk (z₀ ≫ G.hom) ⟶ G := Over.homMk z₀ rfl
  have h1 := h k _ z
  have h2 := h' k _ z
  have hzl : z.left = z₀ := rfl
  rw [hzl, hz, Set.singleton_subset_iff] at h1 h2
  exact h1.symm.trans h2

theorem corr_heckeSet_kill {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {S : Scheme.{0}} (t : SAB H S) {P : Ideal (𝓞 E)} {p i : ℕ} {K : Set t.G.left} (hpP : (p : 𝓞 E) ∈ P)
    (hK : HeckeSet D t P p i K) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ t.G)
    (hz : Set.range z.left ⊆ K) : z ^ p ^ 2 = 1 := by
  have hnat : ∀ {T : Over S} (x : T ⟶ t.G) (n : ℕ), x ≫ t.act.act (n : 𝓞 E) = x ^ n := by
    intro T x n
    induction n with
    | zero =>
      have h := t.act.add 0 0
      rw [add_zero] at h
      have h0 : t.act.act 0 = 1 := by simpa using h
      rw [Nat.cast_zero, pow_zero, h0, MonObj.comp_one]
    | succ n ih => rw [Nat.cast_succ, t.act.add, MonObj.comp_mul, ih, t.act.one, Category.comp_id, pow_succ]
  obtain ⟨C, hC, hH⟩ := hK k x
  have hzC := hH.2.2.1 ((hC z).2 hz)
  have hbar : (p : 𝓞 E) ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hpP
    rwa [map_natCast] at this
  have h := hzC ((p ^ 2 : ℕ) : 𝓞 E) (by
    rw [Nat.cast_pow, pow_two]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hbar)
  rwa [hnat] at h

theorem corr_nonempty : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), 1 ≤ D.p + D.q → admitted l 𝔓 p → Nonempty (Corr Xo 𝔓 p i) := by
  intro E _ _ _ H D l Xo P p i hr hA
  obtain ⟨Z, hZ⟩ := _root_.GlobalTheory.HkFam.exists_kerScheme E H D l Xo P p i hA
  have := Z.et₁
  have := Xo.smooth
  have hXs : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have hs : Smooth (Z.π₁ ≫ Xo.s) := inferInstance
  have hred : IsReduced Z.Hk :=
    (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ hs).1
  obtain ⟨S', π, o', m, τ, hf, he, hsu, hL⟩ :=
    _root_.GlobalTheory.exists_cover_lists_heckeSet E H D l P p i Z.Hk _ Z.o₁ Z.K hA hZ Z.hecke
  have hH' := ((GlobalTheory.heckeSets_pull E H D P p i _ _ _ _ _ m.toSABMap Z.o₁.proper).2 Z.K).1 Z.hecke
  have hq' := _root_.GlobalTheory.hasQuot_of_lists_of_smooth E H D l Xo P p i _ S' _ o' τ _ hr hA inferInstance hL hH'
  obtain ⟨o₂, ψ, hi, hk⟩ := _root_.GlobalTheory.HkFam.hasQuot_descend E H D l Xo P p i Z.Hk S' _ π Z.o₁ o' m Z.K hA Z.hecke he hsu
    inferInstance hq'
  obtain ⟨π₂, ⟨hb, ⟨m₂⟩⟩, -⟩ := Xo.rep _ _ hred o₂
  refine ⟨{ toKerScheme := Z, π₂ := π₂, base₂ := hb, o₂ := o₂, m₂ := m₂, ψ := ψ, isog := hi, ker := hk, univ := ?_ }⟩
  intro S s hS o o' ψ' ⟨hi', K', hk', hH⟩
  have := o'.proper
  have het := (etSet_of_kerSet S _ _ ψ' K' inferInstance hi'.1.2.1 hi'.1.2.2.1 hk').1
  obtain ⟨h, ⟨hh, n₁, hn₁⟩, hu⟩ := Z.rep S s hS o K' het hH
  refine ⟨h, ⟨hh, ?_⟩, ?_⟩
  · obtain ⟨o₃, ⟨n₃⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ _ s h rfl rfl
      (by rw [hh]; simp [spMap]) o₂
    obtain ⟨⟨ψ₃, hψ₃, -⟩, hall⟩ := _root_.GlobalTheory.HkFam.isog_pull E H D l p _ _ _ _ h Z.o₁ o₂ o o₃ n₁ n₃ ψ
    obtain ⟨hi₃, hk₃⟩ := hall ψ₃ hψ₃
    have hk₃' := hk₃ Z.K hi.1.1 hk
    rw [← hn₁] at hk₃'
    obtain ⟨m, hm⟩ := _root_.GlobalTheory.exists_objMap_of_isIsog_of_kerSet E H D l p S s o o' o₃ ψ' ψ₃ K' hA.2.2.1 hA.2.2.2.2 hi' (hi₃ hi) hk' hk₃'
      (corr_heckeSet_kill o.t hA.2.2.2.1 hH)
    have hc := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o₂ o₃ o').2 h (𝟙 S) n₃).1 m
    have hc' : ∀ g : S ⟶ Z.Hk, g = h → (∃ m'' : ObjMap o' o₂ g, m''.toSABMap.φ = m.toSABMap.φ ≫ n₃.toSABMap.φ) →
        ∃ m'' : ObjMap o' o₂ h, m''.toSABMap.φ = m.toSABMap.φ ≫ n₃.toSABMap.φ := by
      rintro g rfl hg
      exact hg
    obtain ⟨n₂, hn₂⟩ := hc' _ (Category.id_comp h) hc
    exact ⟨n₁, n₂, by rw [hn₂, ← Category.assoc, hm, hψ₃]⟩
  · rintro h' ⟨hh', n₁', n₂', e⟩
    have hk₃ := ((_root_.GlobalTheory.HkFam.isog_pull E H D l p _ _ _ _ h' Z.o₁ o₂ o o' n₁' n₂' ψ).2 ψ' e).2 Z.K hi.1.1 hk
    exact hu h' ⟨hh', n₁', corr_kerSet_unique hk' hk₃⟩

end GlobalTheory.HkFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamiliesExist
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.Moduli

theorem siegelFamilies_closed : N0 :=
  _root_.GlobalTheory.SiegelFromSharp.exists_siegelFamily _root_.GlobalTheory.allSixLaws.1 _root_.GlobalTheory.allSixLaws.2.1 _root_.GlobalTheory.Moduli.cube_of_isLB _root_.GlobalTheory.thetaUnifAV_closed

end GlobalTheory.Moduli
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationTriplesCompleteDVRTorsion
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem LN.isAdmissible_of_complete_DVR_charZero (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (hV : LN.CDvr V) :
    LN.admitted V (IsLocalRing.maximalIdeal V) := by
  have := hV.1
  have := hV.2.1
  refine ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, hV.2.1, hV.2.2, inferInstance, ?_⟩
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal V)
  infer_instance

theorem LN.uDvrSt_holds : GlobalTheory.LN.UDvrSt := by
  obtain ⟨L, L2, L3, L4, L5, -⟩ := _root_.GlobalTheory.allSixLaws
  intro E _ _ _ H V _ _ _ hV t hp hs
  have := hV.1
  exact _root_.GlobalTheory.LN.UnifPrime.exists_pelUnif L L2 L3 L4 L5 LN.ega_holds _root_.GlobalTheory.uniformisation_dvr_unconditional _root_.GlobalTheory.LN.pelSt_holds E H V _ (LN.isAdmissible_of_complete_DVR_charZero V hV)
    (by letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal V); infer_instance) t hp hs
    (GlobalTheory.ThetaDvr.thetaNZ_of_polAt L L2 E H V t hp)

end GlobalTheory
end

