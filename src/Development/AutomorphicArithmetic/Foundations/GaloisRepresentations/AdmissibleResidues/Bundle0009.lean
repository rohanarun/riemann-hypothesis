module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.FreeFlag
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.PosOfMulPosOfPos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.Imports
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.Bundle0002
public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.PtOver
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.CobOfCoord
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.BlockPart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0072
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0071
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0067
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ROrdAway
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.AdmissibleResidualOfHyp
section
noncomputable section

open NumberField IsDedekindDomain IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr

namespace UpperTheory.GalN.V

theorem dual_two {Γ k : Type} [Group Γ] [Field k] (W : Γ →* GL (Fin 2) k) : DualTw W (Matrix.GeneralLinearGroup.det.comp W) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp), fun s => by
    have hd : ((Matrix.GeneralLinearGroup.det.comp W s : kˣ) : k) = (W s).val.det := rfl
    rw [hd, Matrix.det_fin_two (W s).val]
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp <;> ring⟩

section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
  {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N}

def IsModularN (_ : Dat Ω K c e ψ) (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l)) : Prop :=
  (∃ f : Af.Newform (2 * e + 1), f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) ∧ WitQ ι W

variable {D : Dat Ω K c e ψ} {ι : Qbar l ≃+* ℂ} {W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l)}

end

def AutEnd2N {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) (η : G ℚ Ω →* ℤˣ)
    (Ψ : G ℚ Ω →* c.Oˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (e : ℕ) (ι : Qbar l ≃+* ℂ) : Prop :=
  ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A]
    (r : G ℚ Ω →* U3.GG (m := 3) (R := A)),
    OrdPt l η Ψ σ g₁ B r → TypeII η (UnitaryThreeInertia.push A.val r) → (∀ g ∈ η.ker, (r g).mat 1 1 = 1) →
    ∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l),
      (∀ g ∈ η.ker, (W g).val = corner (UnitaryThreeInertia.push A.val r g).mat) →
      (W σ).val.trace = 0 →
      (∃ f : Af.Newform (2 * e + 1), f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) ∧ WitQ ι W

end UpperTheory.GalN.V
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConj
section
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

private theorem ps_wt_any {D : Raw Ω c} (h : D.Good) {A : ValuationSubring Ω} (hA : A.valuation (l : Ω) < 1) (i : Fin 4)
    {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) A) (h1 : s ∈ D.ψ.ker) (h2 : s ∈ D.om.ker) :
    D.ps i s = chiO ℚ Ω l c.O s ^ D.wts4 i := by
  have hl : l.Prime := Fact.out
  obtain ⟨u, -, hu⟩ := (UpperTheory.V.Chr.placesQ Ω).2.2 l A _ hl hA (h.pl_over l hl)
  have e : ∀ γ : G ℚ Ω →* c.Oˣ, γ (u⁻¹ * s * u) = γ s := fun γ => by
    rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
  have h3 := (facts D h).2.2.2.1 i (u⁻¹ * s * u) ⟨⟨hu s hs, (e _).trans h1⟩, (e _).trans h2⟩
  rwa [e, e] at h3

private theorem map_psi {ι Γ R R' : Type} [Group Γ] [CommRing R] [CommRing R'] (P : PD ι Γ R) (f : R →+* R') (v : ι) (i : Fin 4)
    (s : Γ) : (P.map f).ψ v i s = f (P.ψ v i s) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [PD.ψ, PD.map, Matrix.mul_apply, adj_apply, map_sum]

private theorem charpoly_conj {H K K' : Type} [Group H] [Field K] [Field K'] (f : K →+* K') {r r' : H →* M4 K}
    (h : IsConj4 r r') (g : H) : (mapRep f r g).charpoly = (mapRep f r' g).charpoly := by
  obtain ⟨u, hu⟩ := h
  show ((r g).map f).charpoly = ((r' g).map f).charpoly
  rw [Matrix.charpoly_map, Matrix.charpoly_map, hu, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

end SlopeTestRemainingChoices
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.IndLoc0
section
open UpperTheory.GalN.V

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2

private theorem near {K : Type} [NormedField K] [IsUltrametricDist K] (d x y z : K) (hd : ‖d - 1‖ < 1) (hx : ‖x - y‖ < 1)
    (hy : ‖y‖ = 1) (hz : ‖z - y‖ < 1) : ‖d * x - z‖ < 1 := by
  have h1 : ‖x‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (x - y) y
    rw [sub_add_cancel] at this
    exact this.trans (max_le hx.le hy.le)
  have h2 : ‖(d - 1) * x‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) h1) hd
  have h3 : d * x - z = (d - 1) * x + ((x - y) + (y - z)) := by ring
  rw [h3]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h2 ?_)
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx ?_)
  rwa [norm_sub_rev]

theorem UpperTheory.GalN.V.indLoc0 :
    AllInd fun {Ω} _ _ _ {l} _ _ _ T _ R δ => ∃ n, LocOk T ⟨twF T R δ, n⟩ ∧ ∃ (m : Fin 4 → ℤ) (b : ℤ) (N : ℕ),
  (∀ i : Fin 3, m i.succ + 2 ≤ m i.castSucc) ∧ Wts0 T (fun i => 2 * m i + b) ⟨twF T R δ, n⟩ ∧ 0 < N ∧
  ∀ g, (δ g ^ 2 * cycBar T.F Ω l g ^ (-b)) ^ N = 1 := by
  intro Ω _ _ _ l _ c D T k₀ _ _ φ ι k t r α β R δ H
  obtain ⟨m, hm, hF⟩ := UpperTheory.induced_flag_condition Ω l c D T k₀ φ ι k t r α β R δ H
  obtain ⟨b, N, U, hN, hδ, hU, hI⟩ := UpperTheory.induced_deletion_condition Ω l c D T k₀ φ ι k t r α β R δ H
  choose n hn using fun v : T.ι => hF (T.pl v) (T.ovl v)
  have key : ∀ v s, adj (n v) * twF T R δ s * n v = (δ s : Qbar l) • (adj (n v) * (R (resQ T.F s) : M4 (Qbar l)) * n v) := by
    intro v s
    have : twF T R δ s = (δ s : Qbar l) • (R (resQ T.F s) : M4 (Qbar l)) := tw_val (R.comp (resQ T.F)) δ s
    rw [this, Matrix.mul_smul, Matrix.smul_mul]
  have key' : ∀ v s i, PD.ψ (⟨twF T R δ, n⟩ : PD T.ι (G T.F Ω) (Qbar l)) v i s =
      (δ s : Qbar l) * (adj (n v) * (R (resQ T.F s) : M4 (Qbar l)) * n v) i i := by
    intro v s i
    show (adj (n v) * twF T R δ s * n v) i i = _
    rw [key, Matrix.smul_apply, smul_eq_mul]
  have ined : ∀ (A : ValuationSubring Ω) (s : G T.F Ω), s ∈ Ine (F := T.F) A → s ∈ Dec (F := T.F) A := fun A s hs => hs.1
  refine ⟨n, ⟨fun v => (hn v).1, ?_, ?_, ?_⟩, m, b, N, hm, ⟨U, hU, ?_⟩, hN, hδ⟩
  · intro v s hs i j hij
    show (adj (n v) * twF T R δ s * n v) i j = 0
    rw [key, Matrix.smul_apply, ((hn v).2 s hs).1 i j hij, smul_zero]
  · intro v s hs i
    obtain ⟨h1, h2⟩ := UpperTheory.inertia_acts_trivially_on_roots_of_unity T.F Ω l H.hyp.good.l_odd (T.pl v) (T.ovl v) s hs
    have h3 : cycBar T.F Ω l s = 1 := by
      simp [cycBar, h2]
    rw [key', (((hn v).2 s (ined _ _ h1)).2 i).2 h1, (hI _ (T.ovl v) s h1).2 h2, h3]
    simp
  · intro v s hs i
    rw [key']
    have hk : resQ T.F s ∈ k₀.fixingSubgroup := H.hyp.spl _ (T.ovl v) hs
    refine near _ _ _ _ (H.δ_one s) (((hn v).2 s hs).2 i).1 ?_ (H.chars.inn s hk i)
    fin_cases i
    · exact H.chars.unit D.ξ _
    · simp
    · exact H.chars.unit D.ξ _
    · simp
  · intro v i s hs
    rw [key', (((hn v).2 s (ined _ _ hs.2)).2 i).2 hs.2, ← Units.val_mul, ← Units.val_pow_eq_pow_val, mul_pow,
      (hI _ (T.ovl v) s hs.2).1 hs.1, ← zpow_natCast, ← zpow_mul, ← zpow_add]
    congr 2
    push_cast
    ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RwOfOrdForm
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial ValuativeRel
open _root_.GlobalTheory GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.SmGL UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.GalN.V.rw_of_ordForm (PH : HypothesesH) (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ξ : G F Ω →* (Qbar l)ˣ) (s c m a π r)
    (H : OrdForm ι ξ s c m a π r) : UpperTheory.GalN.V.RW ι r := by
  have P := PH.toClassicalTheorems
  refine UpperTheory.GalN.V.L.rwwd F Ω l ι 2 r H.cont fun w hl A h => ?_
  obtain ⟨χ, hχ⟩ := H.pol
  obtain ⟨-, wt, HT, -, -, hall⟩ := UpperTheory.GalN.V.exRN (exR PH) F Ω l ι 2 one_le_two π χ H.reg hχ
  have hG := hall r H.cont H.att
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompR P F 2 π w
  obtain ⟨rc, hrc⟩ := P.exists_rec h
  refine hG.ratio w hl A h rc hrc σ hσ ?_
  by_cases hc : c w = 0
  · obtain ⟨v, hv, hf⟩ := H.sph w hc
    let τ := π.locRep w
    let R := MonoidAlgebra ℂ (GL (Fin 2) (w.adicCompletion F))
    have : IsSimpleModule R σ.ρ.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule σ.ρ).1 σ.irred
    have htop : isotypicComponent R τ.asModule σ.ρ.asModule = ⊤ := by
      refine top_le_iff.1 fun y _ => ?_
      have hy : τ.asModuleEquiv y ∈ (⊤ : Submodule ℂ _) := trivial
      rw [← (hiso σ hσ).2] at hy
      rw [← τ.asModuleEquiv.symm_apply_apply y]
      refine Submodule.iSup_induction _ (motive := fun z => τ.asModuleEquiv.symm z ∈ _) hy ?_ ?_ ?_
      · rintro f _ ⟨x, rfl⟩
        let x' : σ.ρ.asModule := σ.ρ.asModuleEquiv.symm x
        let f' := Representation.IntertwiningMap.equivLinearMapAsModule σ.ρ τ
          ⟨f.1, fun g => LinearMap.ext (f.2 g)⟩
        change f' x' ∈ _
        rcases f'.injective_or_eq_zero with h | h
        · have hrange : LinearMap.range f' ≤ isotypicComponent R τ.asModule σ.ρ.asModule :=
            le_sSup ⟨(LinearEquiv.ofInjective f' h).symm⟩
          exact hrange ⟨x', rfl⟩
        · rw [h, LinearMap.zero_apply]
          exact Submodule.zero_mem _
      · rw [τ.asModuleEquiv.symm.map_zero]
        exact Submodule.zero_mem _
      · intro x y hx hy
        rw [τ.asModuleEquiv.symm.map_add]
        exact add_mem hx hy
    have : IsSemisimpleModule R τ.asModule :=
      IsSemisimpleModule.congr (M := isotypicComponent R τ.asModule σ.ρ.asModule)
        (LinearEquiv.ofTop _ htop).symm
    have hTv : ∃ T : τ.asModule →ₗ[R] σ.ρ.asModule, T v ≠ 0 := by
      obtain ⟨m, hm, hvm⟩ : ∃ m : Submodule R τ.asModule, IsCoatom m ∧ v ∉ m := by
        by_contra hn
        push Not at hn
        refine hv ((Submodule.mem_bot (M := τ.asModule) R).1 ?_)
        rw [← IsSemisimpleModule.jacobson_eq_bot R τ.asModule]
        exact Submodule.mem_sInf.2 hn
      obtain ⟨W, hW⟩ := exists_isCompl m
      have : IsSimpleModule R W := isSimpleModule_iff_isAtom.2 (hW.isCoatom_iff_isAtom.1 hm)
      obtain ⟨e⟩ := IsIsotypicOfType.of_isotypicComponent_eq_top htop W
      refine ⟨e.toLinearMap ∘ₗ W.projectionOnto m hW.symm, fun he => hvm ?_⟩
      apply (Submodule.projectionOnto_apply_eq_zero_iff hW.symm).1
      apply e.injective
      rw [e.map_zero]
      exact he
    obtain ⟨T, hTv⟩ := hTv
    let T' := (Representation.IntertwiningMap.equivLinearMapAsModule τ σ.ρ).symm T
    obtain ⟨B, hB⟩ := (satLoc P F 2 w σ).1 ⟨T' v, hTv, fun u hu => by
      have hmem : u ∈ K1 w 0 := by
        obtain ⟨k, rfl⟩ := hu
        refine ⟨k, ?_, rfl⟩
        have : Subsingleton (w.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 0) :=
          Ideal.Quotient.subsingleton_iff.2 (by simp)
        exact Subsingleton.elim (α := Fin 2 → _) _ _
      exact (LinearMap.congr_fun (T'.2 u) v).symm.trans (congrArg T' (hf u hmem))⟩
    exact WD.unr_mono0 _ (UpperTheory.GalN.V.unr_algNorm hrc σ B hB)
  · have hA : ¬ A.valuation (l : Ω) < 1 := fun e => hl (((UpperTheory.V.Base.places F Ω l A).2.2.1 w h).1 e)
    obtain ⟨s₀, hs₀, h0⟩ := IsConcreteLE.not_le_iff_exists.1 fun e => ((H.ram w A h).1 e).elim hc hl
    obtain ⟨g, hg⟩ := UpperTheory.V.Sd.ordAway_n PH F Ω l ι ξ s c m a π r H A hA
    refine UpperTheory.GalN.V.L.monosep F Ω A w h _ (ineIncl h ⟨s₀, hs₀⟩) (deg_ineIncl _) ?_
    have k : UpperTheory.GalN.V.WDN ι r (rc (algNorm σ)) :=
      .of_aw hl H.cont ⟨(hG.away w hl A h rc hrc σ hσ).pol, (hG.away w hl A h rc hrc σ hσ).n0⟩
    have e : (r s₀ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly = (X - C 1) * (X - C (ξ s₀ : Qbar l)) := by
      rw [← Matrix.charpoly_units_conj g, ← Matrix.coe_units_inv, ← Units.val_mul, ← Units.val_mul, hg s₀ hs₀,
        Matrix.charpoly_diagonal, Fin.prod_univ_two]
      rfl
    rw [WD.eig, ← k.charpoly hl, coe_ineIncl, e]
    have h1 : ι (ξ s₀ : Qbar l) ≠ 1 := fun e' => h0 (Units.ext (ι.injective (by simpa using e')))
    rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_sub, map_X, map_C, map_C]
    rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)), roots_X_sub_C, roots_X_sub_C]
    simpa using h1.symm
end
end

