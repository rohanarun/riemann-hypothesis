module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
public import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0782
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0780
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsTemperedGLOfHasSatGL
section
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CuspRep ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CohomologicalConjSelfDualTempered.UnrModel

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem mem_integer_iff (x : w.adicCompletion E) : x ∈ 𝒪[w.adicCompletion E] ↔ x ∈ Formalism.UG.Ov (F := E) w := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [Valuation.mem_integer_iff, ← map_one (valuation _), ← Valuation.vle_iff_le, Valuation.vle_iff_le Valued.v, map_one]
  rfl

theorem range_eq {K : Type} [Field K] {A B : Subring K} (h : A = B) (n : ℕ) :
    (Formalism.UG.bc (n := Fin n) B.subtype).range = (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap A K)).range := by
  subst h; rfl

theorem kgl_eq_ko (n : ℕ) : GlobalTheory.LFun.KGL w (n := n) = GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) :=
  range_eq (SetLike.ext fun x => mem_integer_iff w x) n

theorem isSpherical_of_hasSatGL (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {B : Multiset ℂˣ} (h : GlobalTheory.LFun.HasSatGL w ρ B) :
    GlobalTheory.SmGL.IsSpherical ρ := by
  have h1 := h.1
  unfold GlobalTheory.LGrp.IsSpherical at h1
  unfold GlobalTheory.SmGL.IsSpherical GlobalTheory.SmGL.IsSphericalFor
  rwa [← kgl_eq_ko]

end GlobalTheory.CohomologicalConjSelfDualTempered.UnrModel
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotGoodGenericSign
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory.Hk3.FamModel

open _root_.Formalism.L2.Col

theorem nb_congr {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {P : Ideal (𝓞 E)} {s y : List ℕ}
    (f : inType P s ≃ₗ[𝓞 E] inType P y) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : d.inertSet P s = d.inertSet P y := by
  ext d'
  simp only [DecoSet.inertSet, Set.mem_ofPred_eq, IsInertNbr]
  constructor
  · rintro ⟨⟨⟨e₁⟩, ⟨e₂⟩⟩, hf, hb⟩
    exact ⟨⟨⟨e₁.trans f⟩, ⟨e₂.trans f⟩⟩, hf, hb⟩
  · rintro ⟨⟨⟨e₁⟩, ⟨e₂⟩⟩, hf, hb⟩
    exact ⟨⟨⟨e₁.trans f.symm⟩, ⟨e₂.trans f.symm⟩⟩, hf, hb⟩

theorem op_zero_or {K : Type} [Field K] [NumberField K] [StarRing K] {E : Type} [Field E] [NumberField E]
    [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {S : Col.GSD K} (c : Col.DecoPts S E n ST SG)
    (P : HeightOneSpectrum (𝓞 E)) (s : List ℕ) :
    (Col.heckeI c P.asIdeal s).op = 0 ∨ ∃ y, Col.InertTypeOk n y ∧ (Col.heckeI c P.asIdeal s).op = (Col.heckeI c P.asIdeal y).op := by
  obtain ⟨y, hy₁, hy₂, ⟨f⟩⟩ := GlobalTheory.InertTypeIso.inType_iso_sorted_pos P.asIdeal s
  have hnb : ∀ d, c.nbI P.asIdeal s d = c.nbI P.asIdeal y d := by
    intro d
    rw [DecoPts.nbI, DecoPts.nbI, DecoSet.inertNb, DecoSet.inertNb, nb_congr f]
  have hop : (Col.heckeI c P.asIdeal s).op = (Col.heckeI c P.asIdeal y).op := by
    refine LinearMap.ext fun φ => Subtype.ext (funext fun d => ?_)
    rw [heckeI_op_apply, heckeI_op_apply, hnb]
  by_cases hlen : 2 * y.length ≤ n
  · exact Or.inr ⟨y, ⟨hy₁, hy₂, hlen⟩, hop⟩
  · left
    rw [hop]
    refine LinearMap.ext fun φ => Subtype.ext (funext fun d => ?_)
    rw [heckeI_op_apply]
    have hempty : c.nbI P.asIdeal y d = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun e he => hlen ?_
      rw [DecoPts.mem_nbI, DecoSet.inertNb] at he
      split_ifs at he with hfin
      · exact GlobalTheory.InertRank.two_mul_length_le P y (c.pts d) (c.pts e) hy₂ (hfin.mem_toFinset.mp he)
      · simp at he
    simp [hempty]

theorem csd_zero_or {K : Type} [Field K] [NumberField K] [StarRing K] {E : Type} [Field E] [NumberField E]
    [StarRing E] {n : ℕ} {ST SG' : Finset (HeightOneSpectrum (𝓞 E))} (S : Col.GSD K) (h : S.Ok) (c : Col.DecoPts S E n ST SG')
    (SG : Finset (HeightOneSpectrum (𝓞 E))) (S0 : Set (HeightOneSpectrum (𝓞 E))) (Q : offSubI ST SG SG' S0) (s : List ℕ) :
    heckeCSDI S h c SG S0 (Q, s) = 0 ∨ ∃ y, Col.InertTypeOk n y ∧ heckeCSDI S h c SG S0 (Q, s) = heckeCSDI S h c SG S0 (Q, y) := by
  rcases op_zero_or c (offSubI.lev Q).1 s with h0 | ⟨y, hy, hyeq⟩
  · left
    simp only [heckeCSDI, Col.heckeFamI]
    rw [h0, map_zero]
  · right
    refine ⟨y, hy, ?_⟩
    simp only [heckeCSDI, Col.heckeFamI]
    rw [hyeq]

theorem rank_rows (R : Ranks) : R.N R.m - 1 = R.r + R.m * R.t := by
  have hm := R.two_le_m
  simp only [Ranks.N, Ranks.r, Nat.mul_succ]
  generalize R.m * R.t = x
  omega

theorem inertJunk_col {X : Col.Fields} {Pr : Col.Primes X} {R : Ranks} (W : Col.Wts X Pr.Word R) (Ch : Col.Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)
    (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
    (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
    (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
    (trIv : Fin R.m → (Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) :
    InertJunk (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv) := by
  refine { R := ?_, L := ?_ }
  · intro t Q s
    rcases csd_zero_or (Col.mtildeKGSD W Ch sel t.1) (Col.mtildeKOk W Ch sel t.1 hX) (formPts _ _) Pr.vGs S0 Q s with
      h | ⟨y, hy, hyeq⟩
    · exact Or.inl h
    · refine Or.inr ⟨y, ?_, hyeq⟩
      show Col.InertTypeOk (R.r + R.m * R.t) y
      rw [← rank_rows R]
      exact hy
  · intro j t Q s
    rcases csd_zero_or (Col.mtKGSD W Ch sel t.1 (j.1 + 1)) (Col.mtKOk W Ch sel t.1 hX (j.1 + 1)) (formPts _ _) Pr.vGs S0
        Q s with h | ⟨y, hy, hyeq⟩
    · exact Or.inl h
    · exact Or.inr ⟨y, hy, hyeq⟩

section Real

open Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m)

variable {A3} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end Real

end GlobalTheory.Hk3.FamModel

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AboveL

def resTo {K Ω : Type} (L : Type) [Field K] [Field L] [Field Ω] [Algebra K Ω] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]
    {M : Type} [Monoid M] (r : G K Ω →* M) : G L Ω →* M :=
  r.comp (AlgEquiv.restrictScalarsHom K)

def Restricts {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)} {h : IsPlaceOver A v} {h' : IsPlaceOver A v'}
    (x : WD h) (x' : WD h') : Prop :=
  ∃ (n : ℕ) (a : WDRep h (Fin n → ℂ)) (b : WDRep h' (Fin n → ℂ)), WD.mk a = x ∧ WD.mk b = x' ∧ b.N = a.N ∧
    ∀ (σ : Weil h) (σ' : Weil h'), (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) → b.ρ σ' = a.ρ σ

def IneTriv {K Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v} (x : WD h) : Prop :=
  ∀ τ : Ine (F := K) A, x.charPol (ineIncl h τ) = (Polynomial.X - 1) ^ x.lpDim

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {l : ℕ} [Fact l.Prime] {a : ℕ}

end GlobalTheory.AboveL

end
end

