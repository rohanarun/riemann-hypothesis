module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0022
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.Bundle0001
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LatticeDataThicknessBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIntegralOpW
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0021
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalToGlobal.KernelLattices.Bundle0005
public import Formalism.LocalToGlobal.KernelLattices.KerMtPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0004
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Formalism.LocalToGlobal.GroupLattices.StabilizerCount.StabiliserTrivialOfTiedChain
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Formalism.LocalToGlobal.Columns.ChainInstY

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
section
noncomputable section

namespace GlobalTheory.Pdv

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def ColNorm : Prop :=
  ∀ a, B.R.m ≤ (I.cst a).A ∧ (I.cst a).M ≤ B.R.m ∧
    ∀ j, j ≤ B.R.m - 2 + 1 → ∀ (b : (I.idx a).β j) (P : rowSG (B.primes X) I.sel (I.tup a)), P.1 ∈ (B.primes X).vGs → (I.idx a).h j b P = 1

variable (l : I.Laws) (Z : TC.Later B (I.cols l))

def stabStd (u : B.Word) (a : I.ι) : GlobalTheory.KerJ.StabDat ((I.rec7 l Z).chTw u a) := fun i c =>
  {g | ∃ s : (I.stp u a i).Stab c, g = ((((I.stp u a i).gam c.1 s.1 : GL (Fin (B.R.N i)) B.host.E) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E),
    B.embLL (((I.stp u a i).chr c.1 s.1 : B.LLˣ) : B.LL))}

def RdStd (u : B.Word) (a : I.ι) (r : KerRead ((I.rec7 l Z).chTw u a) B.fields) : Prop :=
  (∀ i c, r.N i c = ((I.stp u a i).rep c).1.1.deco.1.N) ∧
    ∀ i, i < B.R.m → ∀ c c' x, r.Xi i c c' x = B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1
      ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') x)

def StdRd {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
    {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u a, ∃ r : KerRead ((I.rec7 l Z).chTw u a) B.fields, HEq (t.rd u a) r ∧ RdStd I l Z u a r

end GlobalTheory.Pdv

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DivisionOfDeterminantCharacter
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.RoadW GlobalTheory.CongL Polynomial

namespace GlobalTheory.RoadWGeo

def Lacunary (J : Finset ℤ) : Prop :=
  ∀ A B : Finset ℤ, A ⊆ J → B ⊆ J → Disjoint A B → A.Nonempty → B.Nonempty →
    (B.card : ℤ) * A.sum id ≠ (A.card : ℤ) * B.sum id

theorem lacunary_of_growth {J : Finset ℤ} (hpos : ∀ x ∈ J, 0 < x) (hg : ∀ x ∈ J, ∀ y ∈ J, x < y → (J.card : ℤ) * x < y) :
    Lacunary J := by
  classical
  have key : ∀ A B : Finset ℤ, A ⊆ J → B ⊆ J → B.Nonempty → ∀ m ∈ A, (∀ b ∈ B, b < m) →
      (A.card : ℤ) * B.sum id < (B.card : ℤ) * A.sum id := by
    intro A B hA hB hBn m hm hlt
    have h1 : m ≤ A.sum id := Finset.single_le_sum (f := id) (fun x hx => (hpos x (hA hx)).le) hm
    have hc : (A.card : ℤ) ≤ J.card := by exact_mod_cast Finset.card_le_card hA
    have h2 : ∑ b ∈ B, (A.card : ℤ) * b < ∑ _b ∈ B, m := by
      refine Finset.sum_lt_sum_of_nonempty hBn fun b hb => ?_
      have := hg b (hB hb) m (hA hm) (hlt b hb)
      have := mul_le_mul_of_nonneg_right hc (hpos b (hB hb)).le
      linarith
    rw [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at h2
    have h3 : (B.card : ℤ) * m ≤ B.card * A.sum id := mul_le_mul_of_nonneg_left h1 (by positivity)
    exact lt_of_lt_of_le h2 h3
  intro A B hA hB hd hAn hBn
  have hne : (A ∪ B).Nonempty := hAn.mono Finset.subset_union_left
  have hmax : ∀ x ∈ A ∪ B, x ≤ (A ∪ B).max' hne := fun x hx => Finset.le_max' _ _ hx
  rcases Finset.mem_union.1 (Finset.max'_mem _ hne) with hm | hm
  · refine (key A B hA hB hBn _ hm fun b hb => lt_of_le_of_ne (hmax b (Finset.mem_union_right _ hb)) ?_).ne'
    intro e
    exact Finset.disjoint_left.1 hd hm (e ▸ hb)
  · refine (key B A hB hA hAn _ hm fun b hb => lt_of_le_of_ne (hmax b (Finset.mem_union_left _ hb)) ?_).ne
    intro e
    exact Finset.disjoint_left.1 hd hb (e ▸ hm)

theorem not_lacunary_three (k : ℤ) : ¬ Lacunary ({k, k + 1, k + 2} : Finset ℤ) := by
  intro h
  have h02 : k ≠ k + 2 := by omega
  refine h {k, k + 2} {k + 1} ?_ ?_ ?_ (by simp) (by simp) ?_
  · intro x; simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  · intro x; simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  · simp only [Finset.disjoint_singleton_right, Finset.mem_insert, Finset.mem_singleton]; omega
  · rw [Finset.sum_pair h02, Finset.card_pair h02]; simp; ring

def wtJumps {a : ℕ} (lam : DomWeight a) : Finset ℤ :=
  Finset.univ.image fun k : Fin a => ((k : ℕ) : ℤ) - lam.w k

theorem strictMono_jump {a : ℕ} (lam : DomWeight a) : StrictMono fun k : Fin a => ((k : ℕ) : ℤ) - lam.w k := by
  intro i j hij
  have h1 := lam.anti hij.le
  have h2 : (i : ℕ) < j := hij
  simp only
  omega

theorem card_wtJumps {a : ℕ} (lam : DomWeight a) : (wtJumps lam).card = a := by
  rw [wtJumps, Finset.card_image_of_injective _ (strictMono_jump lam).injective]; simp

theorem wtJumps_val {a : ℕ} (lam : DomWeight a) :
    (wtJumps lam).val.map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map (fun z => ((a : ℂ) - 1) / 2 - z) := by
  rw [wtJumps, Finset.image_val_of_injOn (strictMono_jump lam).injective.injOn, infOfWeight, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun k _ => ?_
  simp only [Function.comp]
  push_cast
  ring

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime]

def ESAt {d : ℕ} (ι : Qbar l ≃+* ℂ) (ρ : G E Ω →* GL (Fin d) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂ) :
    Prop :=
  ∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ s ∈ Ine (F := E) A, ρ s = 1) ∧
    ∀ σ : G E Ω, IsFrob A (normV w) σ →
      aeval (ρ σ⁻¹ : Matrix (Fin d) (Fin d) (Qbar l)) (((B.map fun b => X - C b).prod).map ι.symm.toRingHom) = 0

def LacWtAt {a : ℕ} (ι : Qbar l ≃+* ℂ) (v' : HeightOneSpectrum (𝓞 E)) (U : Submodule ℂ (UA E a → ℂ)) : Prop :=
  ∃ τ : E →+* ℂ, OverPl ι τ v' ∧ ∃ lam : DomWeight a, HasWeightAt U τ lam ∧ Lacunary (wtJumps lam)

end GlobalTheory.RoadWGeo

namespace GlobalTheory.Published

open GlobalTheory.RoadWGeo

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
section
noncomputable section

namespace GlobalTheory.Pdv

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Host NumberField IsDedekindDomain

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

def At (ex : Extra D L hT Gi Gl K Y cX) (E : KerEnt D Y ex.tw) : Prop :=
  (E.UnUnit ∧ OrbitPlaces.KmapRat E ∧ OrbitPlaces.KFi D ex.tw ∧ OrbitPlaces.Stab0 D) ∧
    ∃ (ep : _) (be : _) (sg : _),
      OrbitPlaces.EvenConditionsInert (OrbitPlaces.ofKer (nuRowOK D) E ep be sg) Y ∧ OrbitPlaces.EvenConditionsAtC (OrbitPlaces.ofKer (nuRowOK D) E ep be sg) Y ∧
      OrbitPlaces.OrbitBoundWithoutOperator (OrbitPlaces.ofKer (nuRowOK D) E ep be sg) Gi K ∧ OrbitPlaces.JetIntegralityBis (OrbitPlaces.ofKer (nuRowOK D) E ep be sg) Y ∧
      OrbitPlaces.ThetaKernelShapeAtD (OrbitPlaces.ofKer (nuRowOK D) E ep be sg) Y ∧ OrbitPlaces.Shape D L Gi (OrbitPlaces.ofKer (nuRowOK D) E ep be sg)

variable {ex : Extra D L hT Gi Gl K Y cX}

def IsEntC (t : KerEntTied ex) : Prop :=
  ∃ (P : Examples₂.EntPl D) (B : PlaceMatrixFamily D) (h : KerEntHyp P t.O B Y ex.tw), t.ent = kerEntC P t.O B h

structure Duty (t : KerEntTied ex) : Prop where
  col : GlobalTheory.KerJ.ColSide t
  entC : IsEntC t
  rk : t.RK
  forms : ∃ t' : KerEntTied ex, GlobalTheory.KerJ.ColSide t' ∧ GlobalTheory.KerJ.FormsPin t'

end GlobalTheory.Pdv

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsRegAlgTwistOfHalfIntegral
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong

namespace GlobalTheory.Row9

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E]

def FieldOK (l : ℕ) (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  (∃ x : E, ∃ d : ℕ, 0 < d ∧ x ^ 2 = -(d : E)) ∧ Even (Module.finrank ℚ (maximalRealSubfield E)) ∧
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) ∧
    (∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → IsSplitAt w) ∧
    ∃ w₁ w₂ w₃ : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₁.asIdeal ∧ ((l : ℕ) : 𝓞 E) ∈ w₂.asIdeal ∧
      ((l : ℕ) : 𝓞 E) ∈ w₃.asIdeal ∧ Apart w₁ w₂ ∧ Apart w₁ w₃ ∧ Apart w₂ w₃

def SatU {a : ℕ} (U : Submodule ℂ (UA E a → ℂ)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) : Prop :=
  IsSplitAt w ∧ ∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)),
    IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ ∧ GlobalTheory.LFun.HasSatGL w σ.ρ B

def SphG (c : GlobalTheory.RoadU.Sph) {l : ℕ} [Fact l.Prime] {a : ℕ} (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l))
    (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) (inf : (E →+* ℂ) → Multiset ℂ) : Prop :=
  match c with
  | .unr => ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat a (normV w) B)
  | .dR => ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Pst.Induces Bw →
      IsdRAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
        ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' → ∀ J : Multiset ℤ,
          J.map (fun n : ℤ => (n : ℂ)) = (inf (ι.toRingHom.comp τ)).map (fun z => ((a : ℂ) - 1) / 2 - z) →
          IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ J
  | .crys => ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Pst.Induces Bw →
      IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype)
  | .phi => ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
      ∀ g : Weil h, (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).charPol g = (GlobalTheory.RoadU.satWD h a B).charPol g

def CoreUFor (m : ℕ) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), FieldOK l E →
    ∀ U : Submodule ℂ (UA E m → ℂ), IsAutRepU U → ∀ lam : (E →+* ℂ) → DomWeight m, (∀ τ, HasWeightAt U τ (lam τ)) →
    ∃ r : G E Ω →* GL (Fin m) (Qbar l), Continuous r ∧ IsSSRep r ∧
      ∀ w B, SatU U w B → ∀ c, SphG c ι r w B fun τ => infOfWeight (lam τ)

def CoreU : Prop := ∀ m : ℕ, Odd m → CoreUFor m

def HalfIntegral {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (α : CG K 1) : Prop :=
  ∀ τ, ∀ z ∈ α.infChar τ, ∃ k : ℤ, z = (k : ℂ) + 1 / 2

namespace Basic

section Sum

variable {Γ K : Type} [Group Γ] [Field K] {n k : ℕ} (r : Γ →* GL (Fin n) K) (ν : Fin k → (Γ →* Kˣ))

end Sum

variable {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]

end Basic

end GlobalTheory.Row9

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LimWPhi
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong MvPolynomial

namespace GlobalTheory.CongL

def DGen (a : ℕ) : MvPolynomial (Fin a) ℤ :=
  (∏ i : Fin a, ∏ j : Fin a, if i = j then 1 else ∏ c ∈ Finset.range a, (X i ^ (c + 1) - X j ^ (c + 1))) *
  (∏ i : Fin a, ∏ j : Fin a, ∏ k : Fin a, if j = i ∨ j = k then 1 else (X i * X k - X j ^ 2)) *
  (∏ m ∈ (Finset.univ : Finset (Fin a → Fin (a + 1))).filter (fun m => (∑ i, (m i : ℕ)) = a ∧ m ≠ fun _ => 1),
    ((∏ i, X i ^ (m i : ℕ)) - ∏ i, X i))

def GapJ (a : ℕ) (J : Multiset ℤ) : Prop :=
  ∀ i : ℕ, i + 1 < a →
    (J.sort (· ≤ ·)).getD (i + 1) 0 - (J.sort (· ≤ ·)).getD 0 0 > (a : ℤ) * ((J.sort (· ≤ ·)).getD i 0 - (J.sort (· ≤ ·)).getD 0 0)

def WtLac : SeedWtU := fun E _ _ _ l _ a ι w₀ v' U U' =>
  SameWtOff ι w₀ v' U U' ∧ ∃ τ₀ : E →+* ℂ, OverPl ι τ₀ v' ∧ ∀ lam, HasWeightAt U' τ₀ lam → ∀ J : Multiset ℤ,
    J.map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map (fun z => ((a : ℂ) - 1) / 2 - z) → GapJ a J

end GlobalTheory.CongL

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
section
noncomputable section

namespace GlobalTheory.TwV

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG _root_.Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  (A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E)

abbrev UA (D : D7) (i : ℕ) (hi : i ≤ D.R.m) := UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)

def iotaOf (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (P : t.Pr.vT (t.word u)) (v : HeightOneSpectrum (𝓞 D.host.F))
    (h : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) : ((St i hi).K β).lev.fM v h →+ 𝓞 t.X.E ⧸ P.1.asIdeal :=
  Classical.epsilon fun ι => ∀ c, (St i hi).chOf c = β → FunMoved t.seam ((St i hi).K β).lev P v h ι (A.mov i hi c) (A.pt i hi c).deco.1

structure IsPtAd (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x : UA D i hi) (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i) : Prop where
  lat : t.seam.lat p.deco.1.N = latCo D.sp (gramN D i hi) (A.crd i hi) a x.1 ((St i hi).K β).lev.Lb
  frame : ∀ P : SB t μ, NearAt (seamP t.seam P.1) ((t.cst μ).D P)
    (ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P)) (seamGL t.seam (frsF t.sel (t.tup μ) p P))
  fnl : ∀ (P : t.Pr.vT (t.word u)) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal),
    IsOver v (seamP t.seam P.1) →
      FunMoved t.seam ((St i hi).K β).lev P v h (iotaOf A i hi β P v h) (ratA D.host.F (A.crd i hi) * x.1) p.deco.1

def y0At (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (P : SB t μ) : Sp t.X.E (D.R.N i) :=
  if h : i = t.m2 + 1 then (by subst h; exact A.y0 β P) else 0

def cosetOf (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i) : Set (Sp t.X.E (D.R.N i)) :=
  {y | ∀ P : SB t μ, SameCoset t.sel (t.tup μ) (t.cst μ) P ((frsF t.sel (t.tup μ) p P).symm y) (y0At A i hi β P)}

def xiPt (i : ℕ) (hi : i + 1 ≤ D.R.m) (β : (St i (Nat.le_of_succ_le hi)).Ch) (β' : (St (i + 1) hi).Ch)
    (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i) (p' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (i + 1))
    (z : HomE t.X.E (D.R.N i) (D.R.N (i + 1))) : t.X.K :=
  if h : i < t.m2 then
    XiEntry t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (A.ib i hi β) (A.ib (i + 1) (by have := m_eq t μ; omega) β') p p' z
  else if i = t.m2 then XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (A.ib i hi β) p p' (cosetOf A (i + 1) hi β' p') z
  else XiTop t.Ch t.sel (t.tup μ) (t.cst μ) i p (cosetOf A i (Nat.le_of_succ_le hi) β p) p' z


open Classical in
def xiAd : AdDatum St := fun i hi β β' x x' z =>
  if h : (∃ p, IsPtAd A a i (Nat.le_of_succ_le hi) β x p) ∧ ∃ p', IsPtAd A a (i + 1) hi β' x' p' then
    t.seam.σ₀ (xiPt A i hi β β' h.1.choose h.2.choose (seamHom t.seam (inFr
      (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
      (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z)))
  else 0


variable (t u μ) in
open Classical in
def muOf (j : ℕ) (x : (AfE D.host.F D.host.E)ˣ) : ℂ :=
  if h : ∃ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y.1 = x then (((t.O u μ).mt j (dtU h.choose) : ℂˣ) : ℂ) else 0

def PtEx : Prop := ∀ i hi β x, ∃ p, IsPtAd A a i hi β x p

def PtAway (i : ℕ) (hi : i + 1 ≤ D.R.m) : Prop :=
  ∀ β β' x x' x₁ x₁' p p' p₁ p₁', IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
    IsPtAd A a i (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (i + 1) hi β' x₁' p₁' →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1 ∧
      bc (prV (E := D.host.E) v) x₁'.1 = bc (prV (E := D.host.E) v) x'.1) → xiPt A i hi β β' p₁ p₁' = xiPt A i hi β β' p p'

def LevAt (i : ℕ) (hi : i + 1 ≤ D.R.m) : Prop :=
  ∀ β β' x x' x₁ x₁' (κ : ((St i (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (i + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 → ∀ z,
    muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ'.1) * ((((St i _).K β).lev.chi κ : ℂˣ) : ℂ) * xiAd A a i hi β β' x₁ x₁' z =
      muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * ((((St (i + 1) hi).K β').lev.chi κ' : ℂˣ) : ℂ) * xiAd A a i hi β β' x x' z

def RatLaw : Prop :=
  ∀ i hi β β' x x' x₁ x₁', ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)),
    ∀ γ' ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (i + 1) hi), x₁.1 = ratA D.host.F γ * x.1 → x₁'.1 = ratA D.host.F γ' * x'.1 →
    ∀ z, xiAd A a i hi β β' x₁ x₁' z = xiAd A a i hi β β' x x' (inFr
      (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)
      (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ') z)

def SizeLaw : Prop :=
  ∀ i hi β β' x x', DatLoc D t.cc (ssRec t u μ) (t.rd u μ).lev
      (latK D.sp (gramN D i (Nat.le_of_succ_le hi)) a x.1 ((St i _).K β).lev.Lb)
      (latK D.sp (gramN D (i + 1) hi) a x'.1 ((St (i + 1) hi).K β').lev.Lb) (xiAd A a i hi β β' x x') ∧
    ∀ z, xiAd A a i hi β β' x x' z ≠ 0 → z ∈ divLat (t.rd u μ).lev (homAt (ssRec t u μ)
      (latK D.sp (gramN D i (Nat.le_of_succ_le hi)) a x.1 ((St i _).K β).lev.Lb)
      (latK D.sp (gramN D (i + 1) hi) a x'.1 ((St (i + 1) hi).K β').lev.Lb))


variable (t u μ) in
def MuLaw : Prop :=
  ∀ i (hi : i < D.R.m),
    (∀ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det y.1) = (((t.O u μ).mt (i + 1) (dtU y) : ℂˣ) : ℂ)) ∧
    (muOf t u μ dtU (i + 1) 1 = 1 ∧ ∀ x ∈ U1 (sigD D), ∀ y ∈ U1 (sigD D),
      muOf t u μ dtU (i + 1) (x * y) = muOf t u μ dtU (i + 1) x * muOf t u μ dtU (i + 1) y) ∧
    (∀ x ∈ U1 (sigD D), muOf t u μ dtU (i + 1) x ∈ TaylorLogMetric.Qbar) ∧
    (∀ x ∈ U1 (sigD D), x ∈ intU D.host.F D.host.E →
      (∀ v, UnderSB t μ v → prV (E := D.host.E) v (x : AfE D.host.F D.host.E) = 1) → muOf t u μ dtU (i + 1) x = 1) ∧
    ∃ e : D.what₂.Tau → ℤ, (∀ τ, ((e τ : ℤ) : ℚ) = (D.hc τ).e ⟨i, hi⟩) ∧
      ∀ z : D.host.Eˣ, (z : D.host.E) * D.host.conj (z : D.host.E) = 1 →
        muOf t u μ dtU (i + 1) (ratId D.host.F D.host.E z) = ∏ τ, TaylorLogMetric.embT D τ (z : D.host.E) ^ e τ

end GlobalTheory.TwV

def GlobalTheory.TwV.UnderTie (Q : ∀ {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC} {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y cX}
    {t : Formalism.L2.Ker.KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : GlobalTheory.TwU.ChainCharts D u μ}, GlobalTheory.TwU.AdData t u μ St →
    ((letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) → NumberField.RingOfIntegers D.host.E → Prop) : Prop :=
  ∀ {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC} {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y cX}
    {t : Formalism.L2.Ker.KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : GlobalTheory.TwU.ChainCharts D u μ} (A : GlobalTheory.TwU.AdData t u μ St)
    (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : NumberField.RingOfIntegers D.host.E),
    GlobalTheory.TwU.AdPins A dtU → GlobalTheory.TwU.AdTie A dtU a → Q A dtU a

end
end

