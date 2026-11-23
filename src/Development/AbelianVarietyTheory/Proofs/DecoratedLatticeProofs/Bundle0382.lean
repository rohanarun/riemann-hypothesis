module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0455
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelContainsDeepCongruenceAtBadPrime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0438
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDeltaPsi
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0351
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValDetSubOneLt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTrivialCharLevelEltRationalAtTwistPrimes
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

open Formalism.L2.DIV Formalism.L2.Col Formalism.UG GlobalTheory.Mem.Col2.AdT GlobalTheory.Mem.Col2.TC

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.LevelAll

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

theorem adAt_one_apply (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (r s : Fin n) :
    adAt F P ((1 : Matrix (Fin n) (Fin n) (AfE F E)) r s) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s := by
  rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp

theorem conj_bound (hc : CMData F E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1) {u : GL (Fin n) (AfE F E)}
    (hu : u ∈ UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)) (P : HeightOneSpectrum (𝓞 E)) (ε : WithZero (Multiplicative ℤ)) (hε : ε < 1)
    (hP : ∀ r s, Valued.v (adAt F P (u.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ ε) (r s : Fin n) :
    Valued.v (adAt F (conjPrime₂ P) (u.1 r s) - (1 : Matrix (Fin n) (Fin n) ((conjPrime₂ P).adicCompletion E)) r s) ≤ ε := by
  subst hJ
  have hinv : ((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) =
      1 + cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1) := by
    have h : cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) (u : Matrix (Fin n) (Fin n) (AfE F E)) *
        ((1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))) * (u : Matrix (Fin n) (Fin n) (AfE F E)) =
        (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) := hu
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at h
    have e : 1 + cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1) =
        cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) (u : Matrix (Fin n) (Fin n) (AfE F E)) := by
      unfold cT
      rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_sub, Matrix.transpose_one, add_sub_cancel]
    rw [e]
    calc ((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E))
        = (cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) (u : Matrix (Fin n) (Fin n) (AfE F E)) * (u : Matrix (Fin n) (Fin n) (AfE F E))) *
            ((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) := by rw [h, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have h1 : (1 + ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1)) *
      (1 + cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1)) = 1 := by
    rw [← hinv, add_sub_cancel, Units.mul_inv]
  have h2 := congrArg (adAt F (conjPrime₂ P)).mapMatrix h1
  rw [map_mul, map_add (f := _), map_add (f := _), map_one] at h2
  have key := GlobalTheory.Mem.Col2.AdT.Opn.val_inv_le Valued.v _ _ h2 ε hε (fun a b => ?_) r s
  · have e : ((adAt F (conjPrime₂ P)).mapMatrix ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1)) r s =
        adAt F (conjPrime₂ P) (u.1 r s) - (1 : Matrix (Fin n) (Fin n) ((conjPrime₂ P).adicCompletion E)) r s := by
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, map_sub, adAt_one_apply]
    rw [← e]; exact key
  · show Valued.v (adAt F (conjPrime₂ P) (sigR hc.sig (FiniteAdeleRing (𝓞 F) F) (((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1) b a))) ≤ ε
    rw [GlobalTheory.Mem.Col2.valued_sigR hc, GlobalTheory.CharValCompare.conjP_conjP, Matrix.sub_apply, map_sub, adAt_one_apply]
    exact hP b a

end Gen

theorem map_prod_cases {G M κ : Type} [Monoid G] [Monoid M] (f : κ → G) (c : G →* M)
    (hpair : ∀ P P' : κ, P ≠ P' → c (f P) = 1 ∨ c (f P') = 1) :
    ∀ L : List κ, L.Nodup → c (L.map f).prod = 1 ∨ ∃ P ∈ L, c (L.map f).prod = c (f P) := by
  have hall : ∀ (P : κ) (L : List κ), c (f P) ≠ 1 → (∀ P' ∈ L, P' ≠ P) → c (L.map f).prod = 1 := by
    intro P L h1 hL
    induction L with
    | nil => simp
    | cons P' L ih =>
      rw [List.map_cons, List.prod_cons, map_mul, ih fun x hx => hL x (List.mem_cons_of_mem _ hx), mul_one]
      exact (hpair P P' (Ne.symm (hL P' (List.mem_cons.2 (Or.inl rfl))))).resolve_left h1
  intro L
  induction L with
  | nil => intro _; left; simp
  | cons P L ih =>
    intro hL
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, map_mul]
    by_cases h1 : c (f P) = 1
    · rw [h1, one_mul]
      rcases ih hL.2 with h | ⟨P', hP', h⟩
      · exact Or.inl h
      · exact Or.inr ⟨P', List.mem_cons_of_mem _ hP', h⟩
    · rw [hall P L h1 fun P' hP' e => hL.1 (e ▸ hP'), mul_one]
      exact Or.inr ⟨P, List.mem_cons.2 (Or.inl rfl), rfl⟩


set_option maxHeartbeats 12000000 in
theorem exists_level_elt_all : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad), GlobalTheory.Mem.Col2.AdT.ChiFin I l Z S → ∀ (N : ℕ) (g : TC.GA B (B.R.N i)), ∃ z : S.U, S.chi z = 1 ∧ (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P (((g * (show TC.GA B (B.R.N i) from z.1) : TC.GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ ∀ (P : HeightOneSpectrum (𝓞 B.host.E)) (r s : Fin (B.R.N i)), Valued.v (adAt B.host.F P (((show TC.GA B (B.R.N i) from z.1) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s - (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s)) ≤ WithZero.exp (-(N : ℤ)) := by
  intro B X I hOk hPins l Z a T i hi bad S hChi N g
  classical
  have : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  have hgr : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z).2.2.2 i hi).1
  let cP : ∀ P : HeightOneSpectrum (𝓞 B.fields.E), GA B (B.R.N i) →* Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (P.adicCompletion B.fields.E) :=
    fun P => (RingHom.mapMatrix (adAt B.host.F P)).toMonoidHom.comp (Units.coeHom _)
  have cP_apply : ∀ P (g : GA B (B.R.N i)) r s, cP P g r s = adAt B.host.F P ((g : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) := fun _ _ _ _ => rfl
  let ι : S.U →* GA B (B.R.N i) := S.U.subtype
  have hexp : WithZero.exp (-((max N 1 : ℕ) : ℤ)) ≤ WithZero.exp (-(N : ℤ)) := WithZero.exp_le_exp.2 (by omega)
  have hexp1 : WithZero.exp (-((max N 1 : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by omega)
  have hs : ∀ P : SBof I a, GlobalTheory.TwU.seamP (sm I l Z) P.1 = P.1 := fun P => (_root_.GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main I hOk l Z a (B.R.N i) 0 P 1).1
  have hsep : ∀ P P' : SBof I a, P ≠ P' → P.1 ∈ I.Q a → (P'.1 = P.1 ∨ P'.1 = Formalism.L2.Col.conjPrime₂ P.1) → False := by
    intro P P' hne hP h
    rcases h with h | h
    · exact hne (Subtype.ext h.symm)
    obtain ⟨v, hv, hv'⟩ := LevelElt.place_under I hOk hPins l Z a P hP
    apply hv' P' (Ne.symm hne)
    rw [hs] at hv ⊢
    have hc := congrArg HeightOneSpectrum.asIdeal ((GlobalTheory.Mem.Col2.under_eq_iff B.host P.1 P'.1).2 (Or.inr h))
    exact Eq.trans hv hc.symm
  have hsel : ∀ P : SBof I a, ∃ z : S.U, S.chi z = 1 ∧
      (∀ Q : HeightOneSpectrum (𝓞 B.fields.E), cP Q (ι z) = 1 ∨ (P.1 ∈ I.Q a ∧ (Q = P.1 ∨ Q = Formalism.L2.Col.conjPrime₂ P.1))) ∧
      (∀ (Q : HeightOneSpectrum (𝓞 B.fields.E)) r s, Valued.v (cP Q (ι z) r s - (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Q.adicCompletion B.fields.E)) r s) ≤ WithZero.exp (-(N : ℤ))) ∧
      (P.1 ∈ I.Q a → ∃ γ : GL (Fin (B.R.N i)) B.fields.E, ∀ r s, adAt B.host.F P.1 (((g * (show GA B (B.R.N i) from z.1) : GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = algebraMap B.fields.E (P.1.adicCompletion B.fields.E) ((γ : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E) r s)) := by
    intro P
    by_cases hP : P.1 ∈ I.Q a
    · obtain ⟨v, hv, -⟩ := LevelElt.place_under I hOk hPins l Z a P hP
      obtain ⟨z, hz1, hz2, hz3, hz4⟩ := LevelElt.one_prime I hOk hPins l Z a T i hi bad S hChi P hP v hv (max N 1) g 1
      have hzU := ((S.U_eq _).1 z.2).1
      have hbP := ((_root_.GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main I hOk l Z a (B.R.N i) (max N 1) P z.1).2.2).1 hz3
      have hvP := hv
      rw [hs] at hvP
      have hoff : ∀ Q : HeightOneSpectrum (𝓞 B.fields.E), ¬ (Q = P.1 ∨ Q = Formalism.L2.Col.conjPrime₂ P.1) → cP Q (ι z) = 1 := fun Q hQ =>
        Matrix.ext fun r s => by
          rw [cP_apply]
          exact LevelElt.support_one z.1 v hz2 Q (fun hO => hQ ((GlobalTheory.Mem.Col2.under_eq_iff B.host P.1 Q).1
            (HeightOneSpectrum.ext (Eq.trans (Eq.symm hO) hvP)))) r s
      refine ⟨z, hz1, fun Q => ?_, fun Q r s => ?_, fun _ => ?_⟩
      · by_cases hQ : Q = P.1 ∨ Q = Formalism.L2.Col.conjPrime₂ P.1
        · exact Or.inr ⟨hP, hQ⟩
        · exact Or.inl (hoff Q hQ)
      · by_cases hQ : Q = P.1 ∨ Q = Formalism.L2.Col.conjPrime₂ P.1
        · rw [cP_apply]
          rcases hQ with rfl | rfl
          · exact (hbP r s).trans hexp
          · exact (conj_bound (I.rec7 l Z).sp.cm hgr hzU P.1 _ hexp1 hbP r s).trans hexp
        · rw [hoff Q hQ, sub_self, Valuation.map_zero]
          exact zero_le'
      · obtain ⟨γ, hγ⟩ := hz4
        exact ⟨γ, fun r s => by rw [← hγ r s, mul_one]⟩
    · refine ⟨1, map_one _, fun Q => Or.inl (by rw [map_one, map_one]), fun Q r s => ?_, fun h => absurd h hP⟩
      rw [map_one, map_one, sub_self, Valuation.map_zero]; exact zero_le'
  choose zf hzf1 hzf2 hzf3 hzf4 using hsel
  have hpair : ∀ (Q : HeightOneSpectrum (𝓞 B.fields.E)) (P P' : SBof I a), P ≠ P' → cP Q (ι (zf P)) = 1 ∨ cP Q (ι (zf P')) = 1 := by
    intro Q P P' hne
    rcases hzf2 P Q with h | ⟨hP, hQ⟩
    · exact Or.inl h
    rcases hzf2 P' Q with h' | ⟨-, hQ'⟩
    · exact Or.inr h'
    exfalso
    apply hsep P P' hne hP
    rcases hQ with rfl | rfl <;> rcases hQ' with h2 | h2
    · exact Or.inl h2.symm
    · refine Or.inr ?_
      rw [h2, GlobalTheory.CharValCompare.conjP_conjP]
    · exact Or.inr h2.symm
    · have h3 := congrArg Formalism.L2.Col.conjPrime₂ h2
      rw [GlobalTheory.CharValCompare.conjP_conjP, GlobalTheory.CharValCompare.conjP_conjP] at h3
      exact Or.inl h3.symm
  have hone : ∀ P P' : SBof I a, P' ≠ P → cP P'.1 (ι (zf P)) = 1 := by
    intro P P' hne
    rcases hzf2 P P'.1 with h | ⟨hP, hQ⟩
    · exact h
    · exact (hsep P P' hne.symm hP hQ).elim
  have hlistP : ∀ (L : List (SBof I a)), L.Nodup → ∀ P' : SBof I a, cP P'.1 (ι (L.map zf).prod) = if P' ∈ L then cP P'.1 (ι (zf P')) else 1 := by
    intro L
    induction L with
    | nil => intro _ P'; simp
    | cons P L ih =>
      intro hL P'
      rw [List.nodup_cons] at hL
      rw [List.map_cons, List.prod_cons, map_mul, map_mul, ih hL.2]
      by_cases h : P = P'
      · subst h
        simp [hL.1]
      · rw [hone P P' (Ne.symm h)]
        simp [Ne.symm h]
  obtain ⟨w, hw⟩ : ∃ w : S.U, w = ((Finset.univ : Finset (SBof I a)).toList.map zf).prod := ⟨_, rfl⟩
  have hwP : ∀ P : SBof I a, cP P.1 (ι w) = cP P.1 (ι (zf P)) := fun P => by
    rw [hw, hlistP _ (Finset.nodup_toList _) P, if_pos (Finset.mem_toList.2 (Finset.mem_univ _))]
  have hchiw : S.chi w = 1 := by
    rw [hw, map_list_prod]
    refine List.prod_eq_one fun x hx => ?_
    rw [List.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [List.mem_map] at hz
    obtain ⟨P, -, rfl⟩ := hz
    exact hzf1 P
  have hQsub : ∀ P ∈ I.Q a, P ∈ SBof I a := fun P hP => by
    show P ∈ uSG _ _
    exact Finset.mem_union_right _ hP
  refine ⟨w, hchiw, fun P hP => ?_, fun Q r s => ?_⟩
  · obtain ⟨γ, hγ⟩ := hzf4 ⟨P, hQsub P hP⟩ hP
    refine ⟨(γ : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E), fun r s => ?_⟩
    have e0 : cP P (ι w) = cP P (ι (zf ⟨P, hQsub P hP⟩)) := hwP ⟨P, hQsub P hP⟩
    have e1 : cP P (g * ι w) = cP P (g * ι (zf ⟨P, hQsub P hP⟩)) := by rw [map_mul, map_mul, e0]
    have e2 := congrFun (congrFun e1 r) s
    exact (cP_apply P _ r s).symm.trans (e2.trans ((cP_apply P _ r s).trans (hγ r s)))
  · rw [map_sub, adAt_one_apply]
    change Valued.v (cP Q (ι w) r s - (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Q.adicCompletion B.fields.E)) r s) ≤ _
    rcases map_prod_cases zf ((cP Q).comp ι) (hpair Q) _ (Finset.nodup_toList _) with h | ⟨P, -, h⟩
    · rw [← hw] at h
      change cP Q (ι w) = _ at h
      rw [h, sub_self, Valuation.map_zero]; exact zero_le'
    · rw [← hw] at h
      change cP Q (ι w) = _ at h
      rw [h]; exact hzf3 P Q r s

end GlobalTheory.Mem.Col2.AdT.LevelAll

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryChartsAllFinitePlacesFrameLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChartsAll

open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains

theorem exists_charts : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), (IsSplit (E := D.host.E) v → ∃ e, IsSplitChart D.sp.cm.sig V.gram (frameLat V) h e) ∧ (¬ IsSplit (E := D.host.E) v → IsInertAt D.host.F D.host.E v w ∧ Odd (qV D.host.F v) ∧ ∀ c, IsConjAt D.sp.cm.sig h c → ∃ e, IsInertChart D.sp.cm.sig V.gram (frameLat V) h c e) := by
  intro D V v w h
  refine ⟨fun hs => (GlobalTheory.NoExcl.chart V h hs).1, fun hns => ?_⟩
  have hI := GlobalTheory.LFun.exists_isInertChart D.sp.cm.sig (isCMExt_host D) v
  obtain ⟨w₀, hw₀⟩ := (hI.1 (GlobalTheory.VacCoef.isUnram_host D v)).resolve_left hns
  have h₀ : w₀.under (𝓞 D.host.F) = v := GlobalTheory.LFun.under_eq_of_isInertAt hw₀
  obtain rfl : w = w₀ := ((hI.2 w₀ h₀ hw₀).2.2.1 w).1 h
  obtain ⟨-, ⟨c₀, hc₀, -⟩, -, -, H⟩ := hI.2 w h hw₀
  have hfix : Formalism.DivisionValues.conjPl w = w := GlobalTheory.WeilAtPlace.conjPl_eq_of_inert hw₀ h
  have h2 : ((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := fun h2 => GlobalTheory.CoreThree.conj_ne_of_two w h2 hfix
  have hv2 : Valued.v (2 : w.adicCompletion D.host.E) = 1 := by
    rw [← map_ofNat (algebraMap D.host.E (w.adicCompletion D.host.E)) 2, GlobalTheory.Idele.valued_algebraMap,
      ← map_ofNat (algebraMap (𝓞 D.host.E) D.host.E) 2, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 (by exact_mod_cast h2)
  obtain ⟨⟨ϖ, hU⟩, -⟩ := H c₀ hc₀
  refine ⟨hw₀, GlobalTheory.InertLoc.odd_of_v_two hU hv2, fun c hc => ?_⟩
  have hspan : Submodule.span D.host.E (frameLat V : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have hfull : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨x, hx, hx₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e x ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
        intro y hy
        have hxy : V.hT (e x) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
        have hyx : V.hT y (e x) = 0 := by
          rw [(V.herm.eq (e x) y).symm, hxy, map_zero]
        simp [hyx]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e x)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (R := 𝓞 D.host.E) (S := D.host.E)
          (FaithfulSMul.algebraMap_injective _ _) (Field.toIsField _))
    have heq : (frameLat V : Set (Fin V.rank → D.host.E)) =
        V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) :=
      (V.frame.equivFun.toEquiv.image_eq_preimage_symm _).symm
    rw [heq, ← Submodule.map_span, hfull, Submodule.map_top, LinearEquiv.range]
  obtain ⟨e, he, -⟩ := (H c hc).2 V.rank V.gram (frameLat V) (GlobalTheory.NoExcl.isHermND_gram V) (frameLat_fg V)
    hspan (SelfDual.isSelfDualAt_frameLat D V v)
  exact ⟨e, he⟩

end GlobalTheory.ChartsAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteQuotientAnnihilatorStandardLatticeConjHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

noncomputable section

set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.AnnConjHalf

variable {D : D7}

theorem symplO_add_right' (S T : HSp D) (x u v : WO S T) :
    symplO S T x (u + v) = symplO S T x u + symplO S T x v := by
  simp only [symplO, hO, Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem symplO_neg_right' (S T : HSp D) (x u : WO S T) :
    symplO S T x (-u) = -symplO S T x u := by
  simp only [symplO, hO, Matrix.neg_apply, map_neg, mul_neg, neg_mul, Finset.sum_neg_distrib]

theorem symplO_zero_right' (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  simp only [symplO, hO, Matrix.zero_apply, map_zero, mul_zero, zero_mul, Finset.sum_const_zero]

def annHalf (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (E₂ : AE D) : AddSubgroup (WO S T) where
  carrier := {u | IsHalf (cA D E₂) u ∧ ∀ x ∈ stdHom S T, IsHalf E₂ x → ψ (symplO S T x u) = 1}
  zero_mem' := ⟨fun i j => by simp, fun x _ _ => by rw [symplO_zero_right', AddChar.map_zero_eq_one]⟩
  add_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    refine ⟨fun i j => by rw [Matrix.add_apply, mul_add, hu i j, hv i j], fun x hx hxh => ?_⟩
    rw [symplO_add_right', AddChar.map_add_eq_mul, hu' x hx hxh, hv' x hx hxh, mul_one]
  neg_mem' := by
    rintro u ⟨hu, hu'⟩
    refine ⟨fun i j => by rw [Matrix.neg_apply, mul_neg, hu i j], fun x hx hxh => ?_⟩
    rw [symplO_neg_right', AddChar.map_neg_eq_inv, hu' x hx hxh, inv_one]

def stdHalf (S T : HSp D) (f : AE D) : AddSubgroup (WO S T) where
  carrier := {u | u ∈ stdHom S T ∧ IsHalf f u}
  zero_mem' := ⟨zero_mem _, fun i j => by simp⟩
  add_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    exact ⟨add_mem hu hv, fun i j => by rw [Matrix.add_apply, mul_add, hu' i j, hv' i j]⟩
  neg_mem' := by
    rintro u ⟨hu, hu'⟩
    exact ⟨neg_mem hu, fun i j => by rw [Matrix.neg_apply, mul_neg, hu' i j]⟩

theorem half_nsmul {m n : ℕ} {f : AE D} {u : Mx D m n} (hu : IsHalf f u) (N : ℕ) : IsHalf f (N • u) :=
  fun i j => by rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hu i j]

theorem nsmul_eq_zero_WO (S T : HSp D) {N : ℕ} (hN : 0 < N) (v : WO S T) (h : N • v = 0) : v = 0 := by
  ext i j
  have hij : N • v i j = 0 := by
    have := congrFun (congrFun h i) j
    rwa [Matrix.smul_apply] at this
  have hF : (N : D.host.F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hu : IsUnit ((N : ℕ) : AE D) := by
    have := (isUnit_iff_ne_zero.2 hF).map (algebraMap D.host.F (AE D))
    rwa [map_natCast] at this
  rw [nsmul_eq_mul] at hij
  rw [Matrix.zero_apply]
  exact (hu.mul_right_eq_zero).1 hij

theorem ann_conj_half_finite : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u : WO S T, IsHalf (cA D E₂) u → (∀ x ∈ stdHom S T, IsHalf E₂ x → ψ (symplO S T x u) = 1) → ∃ r ∈ R, ∃ v : WO S T, IsHalf (cA D E₂) v ∧ (∀ x ∈ stdHom S T, IsHalf E₂ x → ψ (symplO S T x v) = 1) ∧ u = r + k • v := by
  intro D ψ hψ S T Q E₂ hE k hk
  obtain ⟨N, hN, hup⟩ := _root_.GlobalTheory.HalfAnnStd.exists_nsmul_ann_mem_stdHom D ψ hψ S T Q E₂ hE
  obtain ⟨M, hM, hlow⟩ := GlobalTheory.StdHomOrth.exists_nsmul_orth D ψ hψ S T
  obtain ⟨Q', hQ'⟩ := _root_.GlobalTheory.IdemSumConj.exists_isIdemSum_cA D Q E₂ hE
  have hAL : ∀ a ∈ annHalf ψ S T E₂, N • a ∈ stdHalf S T (cA D E₂) := fun a ha =>
    ⟨hup a ha.1 ha.2, half_nsmul ha.1 N⟩
  have hLA : ∀ l ∈ stdHalf S T (cA D E₂), M • l ∈ annHalf ψ S T E₂ := fun l hl =>
    ⟨half_nsmul hl.2 M, fun x hx _ => hlow x hx l hl.1⟩
  have hfin : ∀ j : ℕ, 0 < j → ∃ R : Finset (WO S T), ∀ u ∈ stdHalf S T (cA D E₂), ∃ r ∈ R,
      ∃ v ∈ stdHalf S T (cA D E₂), u = r + j • v := by
    intro j hj
    obtain ⟨R, hR⟩ := GlobalTheory.HalfStdFin.exists_reps_half_stdHom D S T Q' (cA D E₂) hQ' j hj
    refine ⟨R, fun u hu => ?_⟩
    obtain ⟨r, hr, v, hv, hvh, huv⟩ := hR u hu.1 hu.2
    exact ⟨r, hr, v, ⟨hv, hvh⟩, huv⟩
  obtain ⟨R, hR⟩ := GlobalTheory.addSubgroup_finite_quot_of_commensurable (WO S T) (annHalf ψ S T E₂) (stdHalf S T (cA D E₂))
    N M hN hM (nsmul_eq_zero_WO S T hN) hAL hLA hfin k hk
  refine ⟨R, fun u hu hann => ?_⟩
  obtain ⟨r, hr, v, hv, huv⟩ := hR u ⟨hu, hann⟩
  exact ⟨r, hr, v, hv.1, hv.2, huv⟩

end GlobalTheory.AnnConjHalf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasResOfValSubLt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BaseFn

open _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2.DetSpec

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable [StarRing E] {n : ℕ}

variable {hc : Formalism.BasicNotions.CMData F E} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem fn_eq {p : DecoF E n ST SG Q} {k : GL (Fin n) (AfE F E)} (h : IsPtOf hc k p) (hN : p.deco.1.N = Formalism.L2.Col.stdLat E n) (P : ST)
    (r : Fin n) (hr : r.1 + 1 = n) (c : 𝓞 E)
    (hrow : ∀ i, HasRes P.1 (adAt F P.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 r i)) (if i = r then Ideal.Quotient.mk P.1.asIdeal c else 0))
    (x : Fin n → 𝓞 E) : p.deco.1.f P (fun i => (x i : E)) = Ideal.Quotient.mk P.1.asIdeal (c * x r) := by
  refine HasRes.unique (h.f P _ (hN ▸ (Formalism.L2.Col.mem_stdLat _).2 fun i => ⟨x i, rfl⟩) r hr) ?_
  choose ρ hρ hv using hrow
  refine ⟨∑ i, ρ i * x i, ?_, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_sum, map_mul, hρ, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [Col2.pullV, Matrix.mulVec, dotProduct, map_sum, map_mul, adAt_inclE]
      rw [← Finset.sum_sub_distrib]
      refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_
      show Valued.v (_ * algebraMap E (P.1.adicCompletion E) (algebraMap (𝓞 E) E (x i)) - _) < 1
      rw [← _root_.sub_mul, map_mul, valued_algebraMap]
      exact (mul_le_of_le_one_right' (P.1.valuation_le_one (x i))).trans_lt (hv i)

end Loc

end GlobalTheory.BaseFn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsNormalFr
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

variable {D : D7}

abbrev FYFam {a : XGeo D} {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) : Type :=
  ∀ j c, j + c = l.s + 1 → Frame l.k (Yc D j).rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c)

def IsNormalFr {a : XGeo D} {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (y : YRat a)
    (FY : FYFam l) (sc : ℕ → l.k) : Prop :=
  (∀ j, valuation l.k (sc j) = 1) ∧ (∀ j, sc (j + 1 + 1) = sc j * (ofSplit l.q).xi) ∧
  (∀ j ρ h, valuation l.k ((ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol)) = 1) ∧
  (∀ j ρ h c (hc : j + c = l.s + 1), (ofSplit l.q).IsBesFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j (by omega))
    (FY j c hc)) ∧
  (∀ j ρ h c (hc : j + 1 + c = l.s + 1), (ofSplit l.q).IsJacFrame ((y.jac j ρ h).lev (a.x (j + 1)).vol) (sc j)
    ((ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol)) (l.FX (j + 1) (by omega)) (FY (j + 1) c hc)) ∧
  ∀ h, (y.τ l.s h).map (ofSplit l.q).pr *ᵥ (fun i => (ofSplit l.q).pr (a.ζ₀ i)) =
    (-((ofSplit l.q).xi * sc l.s)) • fun i => (ofSplit l.q).pr ((y.bes l.s 0 h).ζ i)

end GlobalTheory.Fam

end
end

