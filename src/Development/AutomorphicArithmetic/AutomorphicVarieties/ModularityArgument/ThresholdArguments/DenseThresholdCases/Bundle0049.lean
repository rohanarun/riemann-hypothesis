module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TJacqOfU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0041
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdWinA
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.V.Z.Sym.W.RetractionModules
section Rep
private theorem mod_retr {R S M : Type} [Ring R] [AddCommGroup S] [Module R S] [AddCommGroup M] [Module R M]
    [IsSimpleModule R S] (h : ⨆ f : S →ₗ[R] M, LinearMap.range f = ⊤) (x : M) (hx : x ≠ 0) :
    ∃ T : M →ₗ[R] S, T x ≠ 0 := by
  have htop : isotypicComponent R M S = ⊤ := top_le_iff.1 (h ▸ iSup_le fun f => by
    rcases f.injective_or_eq_zero with hi | rfl
    · exact le_sSup ⟨(LinearEquiv.ofInjective _ hi).symm⟩
    · simp)
  haveI : IsSemisimpleModule R M :=
    IsSemisimpleModule.congr (M := isotypicComponent R M S) (LinearEquiv.ofTop _ htop).symm
  have hiso := IsIsotypicOfType.of_isotypicComponent_eq_top htop
  obtain ⟨m, hm, hxm⟩ : ∃ m : Submodule R M, IsCoatom m ∧ x ∉ m := by
    by_contra hn
    push Not at hn
    refine hx ((Submodule.mem_bot R).1 ?_)
    rw [← IsSemisimpleModule.jacobson_eq_bot R M]
    exact Submodule.mem_sInf.2 hn
  obtain ⟨W, hc⟩ := exists_isCompl m
  haveI : IsSimpleModule R W := isSimpleModule_iff_isAtom.2 (hc.isCoatom_iff_isAtom.1 hm)
  obtain ⟨e⟩ := hiso W
  refine ⟨e.toLinearMap ∘ₗ W.projectionOnto m hc.symm, fun h0 => hxm ?_⟩
  simpa using h0
variable {Γ X V : Type} [Group Γ] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
private theorem rep_retr (σ : Representation ℂ Γ X) (hσ : σ.IsIrreducible) (τ : Representation ℂ Γ V)
    (h : ⨆ f : {f : X →ₗ[ℂ] V // ∀ g v, f (σ g v) = τ g (f v)}, LinearMap.range f.1 = ⊤) (x : V) (hx : x ≠ 0) :
    ∃ T : V →ₗ[ℂ] X, (∀ g v, T (τ g v) = σ g (T v)) ∧ T x ≠ 0 := by
  have key := mod_retr (R := MonoidAlgebra ℂ Γ) (S := σ.asModule) (M := τ.asModule) (by
      refine top_le_iff.1 fun y _ => ?_
      have hy : τ.asModuleEquiv y ∈ (⊤ : Submodule ℂ V) := trivial
      rw [← h] at hy
      rw [← τ.asModuleEquiv.symm_apply_apply y]
      refine Submodule.iSup_induction _ (motive := fun z => τ.asModuleEquiv.symm z ∈ _) hy ?_ ?_ ?_
      · rintro f _ ⟨v, rfl⟩
        exact Submodule.mem_iSup_of_mem (Representation.IntertwiningMap.equivLinearMapAsModule σ τ
          ⟨f.1, fun g => LinearMap.ext (f.2 g)⟩) ⟨v, rfl⟩
      · simp
      · intro a b ha hb
        rw [map_add (f := _)]
        exact add_mem ha hb)
  obtain ⟨T, h2⟩ := key x hx
  let T' := (Representation.IntertwiningMap.equivLinearMapAsModule τ σ).symm T
  exact ⟨T'.toLinearMap, fun g v => LinearMap.congr_fun (T'.2 g) v, h2⟩
private theorem ne_zero_rep (τ : Representation ℂ Γ V) {x : V} (hx : x ≠ 0) (g : Γ) : τ g ≠ 0 := fun h => hx (by
  have : τ g⁻¹ (τ g x) = x := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← this, h, LinearMap.zero_apply, map_zero])
private theorem map_dc (σ : Representation ℂ Γ X) (τ : Representation ℂ Γ V) (T : V →ₗ[ℂ] X)
    (hT : ∀ g v, T (τ g v) = σ g (T v)) {x : V} (hx : T x ≠ 0) (K : Subgroup Γ) (a : Γ) :
    T (Hi.dc τ K K a x) = Hi.dc σ K K a (T x) := by
  have hx0 : x ≠ 0 := fun e => hx (by rw [e, map_zero])
  rcases finite_or_infinite (MulAction.orbit K (a : Γ ⧸ K)) with hf | hf
  · haveI := Fintype.ofFinite (MulAction.orbit K (a : Γ ⧸ K))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, map_sum, hT]
  · rw [Hi.dc, Hi.dc, finsum_of_infinite_support, finsum_of_infinite_support]
    · simp
    · rw [Function.support_eq_univ fun _ => ne_zero_rep σ hx _]
      exact Set.infinite_univ
    · rw [Function.support_eq_univ fun _ => ne_zero_rep τ hx0 _]
      exact Set.infinite_univ
end Rep
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.SmGL UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem exists_ps {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin 2) k) V} (hπ : GlobalTheory.PRep.IsSmooth π)
    (hi : π.IsIrreducible) (μ₁ μ₂ : kˣ →* ℂˣ) (L : V →ₗ[ℂ] ℂ) (hL : L ≠ 0)
    (H : ∀ (a d : kˣ) (x : k) v, L (π (Matrix.GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) x) v) =
      ((μ₁ a * μ₂ d : ℂˣ) : ℂ) * L v) :
    ∃ ψ : Fin 2 → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ IsSubquotient π (prinSeries ψ) ∧
      ∀ x : kˣ, ψ 0 x = μ₁ x * (absPow k (1 / 2) x)⁻¹ := by
  set δ : (Fin 2 → kˣ) →* ℂˣ := (deltaHalf k fun _ : Fin 2 => Unit).comp (leviTorus k (Fin 2)).toMonoidHom with hδ
  let χ : (Fin 2 → kˣ) →* ℂˣ := torusChar ![μ₁, μ₂] * δ⁻¹
  have hU : GlobalTheory.PRep.twKer π (unipB k (Fin 2)) 1 ≤ LinearMap.ker L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    obtain ⟨u1, u2⟩ := (mem_unipB k).1 u.2
    have e : (u : GL (Fin 2) k) = Matrix.GeneralLinearGroup.scalar (Fin 2) 1 * aff (1 / 1) (u.1.val 0 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [aff, u2, u1 1 0]
    have := H 1 1 (u.1.val 0 1) v
    rw [← e] at this
    simp [this]
  let l : GlobalTheory.PRep.Jacquet π (unipB k (Fin 2)) →ₗ[ℂ] ℂ := Submodule.liftQ _ L hU
  obtain ⟨v, hv⟩ : ∃ v, L v ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hL (LinearMap.ext hn)
  have hle : ∀ t x, l (jacB π t x) = (χ t : ℂ) * l x := fun t x => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have e : diagT k (Fin 2) t = Matrix.GeneralLinearGroup.scalar (Fin 2) (t 1) * aff (t 0 / t 1) 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [aff, val_diagT, Matrix.GeneralLinearGroup.scalar, mul_div_cancel₀]
    rw [UnramFixed.jacB_apply, jacBU_mk, map_smul, e]
    change _ * L _ = _ * L y
    rw [H, ← mul_assoc, ← Units.val_mul, mul_comm _ (μ₁ _ * _)]
    simp [χ, torusChar_apply, hδ]
  have hs : IsSmoothChar χ := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
      ((isSmooth_jacB hπ (Submodule.Quotient.mk v)).mem_nhds (by simp)) ?_)
    intro g hg
    have hg' : jacB π g (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := hg
    have h := hle g (Submodule.Quotient.mk v)
    rw [hg'] at h
    exact Units.ext (mul_right_cancel₀ (show l (Submodule.Quotient.mk v) ≠ 0 from hv) (h.symm.trans (one_mul _).symm))
  have htc : torusChar (fun i => χ.comp (MonoidHom.mulSingle (fun _ => kˣ) i)) = χ :=
    MonoidHom.ext fun t => by
      rw [torusChar_apply]
      conv_rhs => rw [← Finset.univ_prod_mulSingle t, map_prod]
      rfl
  refine ⟨fun i => χ.comp (MonoidHom.mulSingle (fun _ => kˣ) i),
    fun i => hs.comp _ (continuous_mulSingle (A := fun _ => kˣ) i), ?_, fun x => ?_⟩
  · have key := GlobalTheory.SatakeExists.isSubquotient_of_eigenform hπ hi χ l
      (fun e => hv (LinearMap.congr_fun e (Submodule.Quotient.mk v))) hle
    rw [← htc] at key
    exact key
  · have hd : ∀ (t : Fin 2 → kˣ) i, Matrix.GeneralLinearGroup.det (leviTorus k (Fin 2) t i) = t i := fun t =>
      congrFun ((leviTorus k (Fin 2)).left_inv t)
    have e0 : modExp (fun _ : Fin 2 => Unit) 0 = 1 := by decide
    have e1 : modExp (fun _ : Fin 2 => Unit) 1 = -1 := by decide
    have h1 : δ (Pi.mulSingle 0 x) = absPow k (1 / 2) x := by
      rw [hδ, MonoidHom.comp_apply]
      change deltaHalf k (fun _ : Fin 2 => Unit) (leviTorus k (Fin 2) (Pi.mulSingle 0 x)) = _
      rw [deltaHalf_apply, Fin.prod_univ_two, hd, hd, e0, e1]
      simp
    change torusChar ![μ₁, μ₂] (Pi.mulSingle 0 x) * (δ (Pi.mulSingle 0 x))⁻¹ = _
    rw [h1]
    simp [torusChar_apply]
section Gal
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {h : IsPlaceOver A w}
end Gal
end UpperTheory.V.Z.Sym.W.RetractionModules
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.SmGL UpperTheory.V.Af
open UpperTheory.V.Sd UpperTheory.V.Z.Sym.W.RetractionModules
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem plainAll {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
    {ι : Qbar l ≃+* ℂ} {ξ : G F Ω →* (Qbar l)ˣ} {s c m a π r} (H : OrdForm ι ξ s c m a π r) {wt HT} (hG : UpperTheory.Gal.SV.IsGalRS π ι r wt HT) (w) :
    UpperTheory.V.Z.Win.PlainAtR π w := fun σ hσ =>
  (UpperTheory.V.Z.Win.Birth.ordPlain F Ω l ι ξ s c m a π r H w σ hσ).elim id fun ⟨B, hB⟩ => hG.plain w B hB σ hσ
theorem UpperTheory.V.Z.Sym.W.tieS_a_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Z.Sym.Unl.TieS := by
  intro PH F Ω _ _ _ _ _ _ l _ ι ξ s c m a π r H w hl B hB
  obtain ⟨χ, hχ⟩ := H.pol
  obtain ⟨-, wt, HT, -, -, hall⟩ := _root_.UpperTheory.Gal.SV.exRS_alt PH.toClassicalTheorems F Ω l ι 2 one_le_two π χ H.reg hχ
  exact (hall r H.cont H.att).frob w hl B hB
theorem UpperTheory.V.Z.Sym.W.ordWin_a_alt (PH : _root_.UpperTheory.V.Af.HypothesesH') (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ξ : G F Ω →* (Qbar l)ˣ) (s c m a π r)
    (H : OrdForm ι ξ s c m a π r) : UpperTheory.GalN.V.RW ι r := by
  refine UpperTheory.GalN.V.L.rwwd F Ω l ι 2 r H.cont fun w hl A h => ?_
  obtain ⟨χ, hχ⟩ := H.pol
  obtain ⟨-, wt, HT, -, -, hall⟩ := _root_.UpperTheory.Gal.SV.exRS_alt PH.toClassicalTheorems F Ω l ι 2 one_le_two π χ H.reg hχ
  exact (hall r H.cont H.att).ratio w hl A h (plainAll H (hall r H.cont H.att) w)
theorem UpperTheory.V.Z.Sym.W.tieU_a_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Z.Sym.Unl.TieU := by
  intro PH F Ω _ _ _ _ _ _ l _ ι ξ s c m a π r H w hl n lam hn hl0 hU A h t ht
  have P := PH.toClassicalTheorems
  obtain ⟨χ, hχ⟩ := H.pol
  obtain ⟨-, wt, HT, -, -, hall⟩ := _root_.UpperTheory.Gal.SV.exRS_alt PH.toClassicalTheorems F Ω l ι 2 one_le_two π χ H.reg hχ
  have hG := hall r H.cont H.att
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := _root_.UpperTheory.V.Af.local_comp_real_of_printed_results P F 2 π w
  obtain ⟨v, hv, hf, hUv⟩ := hU
  obtain ⟨T, hT, hTv⟩ := rep_retr σ.ρ σ.irred (π.locRep w) (hiso σ hσ).2 v hv
  obtain ⟨μ₁, μ₂, L, hL, hμ, hlam, hlaw⟩ := _root_.UpperTheory.V.Sd.jacqOfU_alt P F w σ n (Units.mk0 lam hl0) hn
    ⟨T v, hTv, fun u hu => by rw [← hT, hf u hu], by
      rw [Uop, ← map_dc σ.ρ (π.locRep w) T hT hTv, ← Uop, hUv, map_smul, Units.val_mk0]⟩
  obtain ⟨ψ, hψ, hs, hψ0⟩ := exists_ps σ.smooth σ.irred μ₁ μ₂ L hL hlaw
  obtain ⟨b, hb⟩ := GlobalTheory.localArtinExists_holds F Ω A w h
  let g : Weil h := (⟨t, mem_Weil_of_isFrob h ht⟩ : Weil h)⁻¹
  have hdeg : deg g = -1 := by
    rw [deg_inv, deg_eq_one_iff.2 ht]
  have hp := plainAll H hG w σ hσ
  have e1 := _root_.UpperTheory.V.Z.Sym.W.eigW_alt P F Ω l ι 2 r w hl A h b hb σ (hG.loc w σ hσ hp).1 hp ψ hψ hs g
  have h2 : ((r (g : G F Ω)).val.charpoly.map ι.toRingHom).IsRoot
      ((((normV w : ℕ) : ℂ) ^ ((((1 - ((2 : ℕ) : ℝ)) / 2 : ℝ)) : ℂ)) ^ deg g * ((ψ 0 (b g) : ℂˣ) : ℂ)) := by
    have hA := GlobalTheory.SatChar.absPow_art hb ((1 - ((2 : ℕ) : ℝ)) / 2 : ℝ) g
    have hc : -((((2 : ℕ) : ℂ) - 1) / 2) = ((((1 - ((2 : ℕ) : ℝ)) / 2 : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [e1, UpperTheory.V.Z.Sym.W.psPol, Fin.prod_univ_two, hc, ← hA]
    refine Polynomial.IsRoot.def.2 ?_
    rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Units.val_mul, mul_comm ((ψ 0 (b g) : ℂˣ) : ℂ), sub_self, zero_mul]
  have key : (((normV w : ℕ) : ℂ) ^ ((((1 - ((2 : ℕ) : ℝ)) / 2 : ℝ)) : ℂ)) ^ deg g * ((ψ 0 (b g) : ℂˣ) : ℂ) = lam := by
    have hy : ord (w.adicCompletion F) (b g) = 1 := by rw [hb.ord_eq, hdeg, neg_neg]
    have hv0 : Valued.v ((b g : (w.adicCompletion F)ˣ) : w.adicCompletion F) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 (Units.ne_zero _)
    have hv1 : Valued.v ((b g : (w.adicCompletion F)ˣ) : w.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
      rw [SphCompletion.ord_completion] at hy
      rw [← WithZero.exp_log hv0]
      congr 1
      omega
    have hu : IsUnitAt w (b g * (atFin w (unif w))⁻¹) := by
      have h2 := unif_spec w
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hv1, h2]
      exact mul_inv_cancel₀ (by simp)
    have hμy : μ₁ (b g) = μ₁ (atFin w (unif w)) := by
      exact mul_inv_eq_one.1 (by rw [← map_inv, ← map_mul]; exact hμ _ hu)
    have hA := GlobalTheory.SatChar.absPow_art hb (1 / 2 : ℝ) g
    have hq : ((normV w : ℕ) : ℂ) ≠ 0 := by
      have := GlobalTheory.WeilDeligne.one_lt_normV w
      exact_mod_cast (zero_lt_one.trans this).ne'
    have hQ2 : ((normV w : ℕ) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) * ((normV w : ℕ) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) = ((normV w : ℕ) : ℂ) := by
      rw [← Complex.cpow_add _ _ hq]
      norm_num
    have hs' : ((((1 - ((2 : ℕ) : ℝ)) / 2 : ℝ)) : ℂ) = -(((1 / 2 : ℝ)) : ℂ) := by
      push_cast
      norm_num
    have hc : ((1 / 2 : ℂ)) = (((1 / 2 : ℝ)) : ℂ) := by
      push_cast
      rfl
    rw [hdeg] at hA
    rw [hψ0, Units.val_mul, Units.val_inv_eq_inv_val, hc, hA, hμy, hs', hdeg, Complex.cpow_neg]
    have hl' := hlam
    rw [Units.val_mk0] at hl'
    generalize ((normV w : ℕ) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) = Q at hQ2 ⊢
    rw [← hl', ← hQ2]
    simp only [zpow_neg, zpow_one, inv_inv]
    ring
  rw [key] at h2
  refine ⟨ι.symm lam, ?_, by simp⟩
  have h3 : ι.toRingHom (ι.symm lam) = lam := ι.apply_symm_apply lam
  rw [← h3] at h2
  exact (Polynomial.isRoot_map_iff ι.injective).1 h2
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SVPatch
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open _root_.GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Af.Bc GlobalTheory.RealGal UpperTheory.V.Af.ExLib
namespace UpperTheory.Gal.SV
theorem attRes_alt : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : TR.CuspSub F a) (P : CuspSub K a), IsBC π P → ∀ (r : G K Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (K →+* Qbar l) → Multiset ℤ), UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) P ι r wt HT → AttRes π ι K r := by
  intro L F Ω _ _ _ _ _ _ K _ _ _ _ _ _ _ l _ ι a ha π P hBC r wt HT H
  have hloc := _root_.GlobalTheory.T.local_global_compatibility_complex_alt L
  have hsl := _root_.GlobalTheory.RealGal.SatLocProof.main
  refine (hBC.unr.and (eventually_not_mem K l)).mono ?_
  rintro w ⟨hu, hw⟩ f hf
  obtain ⟨B, hB, hBw⟩ := hu (w.under (𝓞 F)) rfl f hf
  refine ⟨B, hB, ?_⟩
  obtain ⟨⟨σ, hσ⟩, hi⟩ := hloc K a P w
  have hS := ((hsl K a w σ).2 _ P.finPart (hi σ hσ) _).1 hBw
  have h1 := frob_of (ι := ι) (r := r) hw σ hS fun A h rc hrc => by
    have g := gdOf K Ω A w h rc hrc a σ ((plainOf K a ha P w).2 ⟨_, hBw⟩ σ hσ)
    rw [← (H.away w hw A h rc hrc σ hσ).tor g.1 g.2]
    exact isWDOf_wdOf (h := h) hw ι (Units.continuous_val.comp H.cont)
  rwa [hf, GlobalTheory.RealGal.AttResProof.algSat_pow] at h1
section Descent
variable {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {a : ℕ}
theorem local_condition_at_place_of_decomposition_le_range (L : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (ha : 1 ≤ a) {K : Type} [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω]
    [IsScalarTower F K Ω] [IsAlgClosure K Ω] {ι : Qbar l ≃+* ℂ} {π : TR.CuspSub F a} {P : CuspSub K a} (hBC : IsBC π P)
    {r : G F Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (K →+* Qbar l) → Multiset ℤ}
    (hG : UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) P ι (r.comp (res F Ω K)) wt HT) {v : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω}
    (h : IsPlaceOver A v) (hdec : Dec (F := F) A ≤ (res F Ω K).range) {HTF : (F →+* Qbar l) → Multiset ℤ}
    (hHT : ∀ τ : K →+* Qbar l, HT τ = HTF (τ.comp (algebraMap F K))) : At π ι r HTF h := by
  obtain ⟨w, h', i, hi⟩ := GlobalTheory.T.exists_place_completion_iso F Ω K v A h hdec
  have hlw : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ((l : ℕ) : 𝓞 K) ∉ w.asIdeal := fun hl hw => by
    apply hl
    have e1 := (h ((l : ℕ) : 𝓞 F))
    have e2 := (h' ((l : ℕ) : 𝓞 K))
    simp only [map_natCast] at e1 e2
    exact e1.1 (e2.2 hw)
  have ST := splitTr F K a ha π P hBC v w i ⟨hi.cont, hi.loc⟩
  obtain ⟨⟨σ', hσ'⟩, -⟩ := _root_.GlobalTheory.T.local_global_compatibility_complex_alt L K a P w
  obtain ⟨rc', hrc'⟩ := recTExists K Ω A w h'
  obtain ⟨S, hS, -⟩ := GlobalTheory.T.place_over_transport_ring_iso_symm F Ω A v h K Ω A w h' _ _ i hi
  have inj : ∀ {x y : WD h} {x' y' : WD h'}, WDRel (RingEquiv.refl Ω) x x' → WDRel (RingEquiv.refl Ω) y y' → x' = y' → x = y :=
    fun hx hy e => S.injective (by rw [(hS _ _).1 hx, (hS _ _).1 hy, e])
  have up : ∀ σ, π.IsLocComp v σ → GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) → Gd (rc' (algNorm σ')) := fun σ hσ hp => by
    obtain ⟨e, he⟩ := hBC.split v w i hi.cont hi.loc σ σ' hσ hσ'
    have hplain : GlobalTheory.RoadU.PlainTor (IrrGL.of σ'.ρ σ'.smooth σ'.irred) := by
      have hi' := GlobalTheory.LocalFieldIso.continuous_symm i hi.cont
      obtain ⟨s, hS, h1, hU⟩ := hp
      have hρ := hS.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm
      have hg (g : GL (Fin a) (w.adicCompletion K)) :
          Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map i.symm.toRingHom g) = g :=
        Units.ext (Matrix.ext fun _ _ => i.apply_symm_apply _)
      let φ : Representation.Equiv
          (σ.ρ.comp (Matrix.GeneralLinearGroup.map (n := Fin a) i.symm.toRingHom)) σ'.ρ :=
        GlobalTheory.LocGL.equivOfBijective ⟨e.toLinearMap, fun g => LinearMap.ext fun x => by
          change e (σ.ρ (Matrix.GeneralLinearGroup.map i.symm.toRingHom g) x) = σ'.ρ g (e x)
          rw [he, hg]⟩ e.bijective
      have hS' := (GlobalTheory.SuppIne.hasSupport_comp i hi.cont hi' hρ).of_equiv φ
      refine ⟨s.map (GlobalTheory.SuppIne.trGL i hi'), hS'.of_equiv (IrrGL.equivOf σ'.ρ σ'.smooth σ'.irred), ?_, ?_⟩
      · intro y hy
        obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
        exact h1 z hz
      · intro y hy z hz heq
        obtain ⟨y₀, hy₀, rfl⟩ := Multiset.mem_map.1 hy
        obtain ⟨z₀, hz₀, rfl⟩ := Multiset.mem_map.1 hz
        obtain ⟨χ, hχ, rfl⟩ := GlobalTheory.RoadU.PlainChars.exists_eq_ofChar y₀ (h1 y₀ hy₀)
        obtain ⟨ψ, hψ, rfl⟩ := GlobalTheory.RoadU.PlainChars.exists_eq_ofChar z₀ (h1 z₀ hz₀)
        have smooth_comp {θ : (v.adicCompletion F)ˣ →* ℂˣ} (hθ : GlobalTheory.SmGL.IsSmoothChar θ) :
            GlobalTheory.SmGL.IsSmoothChar (θ.comp (Units.map i.symm.toRingHom.toMonoidHom)) :=
          IsOpen.preimage (f := Units.map i.symm.toRingHom.toMonoidHom) (Continuous.units_map _ hi') hθ
        rw [GlobalTheory.DegOneChar.trGL_ofChar i hi' χ hχ (smooth_comp hχ),
          GlobalTheory.DegOneChar.trGL_ofChar i hi' ψ hψ (smooth_comp hψ), IrrGL.nu, IrrGL.tw_ofChar,
          IrrGL.ofChar_inj] at heq
        refine hU _ hy₀ _ hz₀ ?_
        rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj]
        refine MonoidHom.ext fun t => ?_
        have h4 := DFunLike.congr_fun heq (Units.map i.toRingHom.toMonoidHom t)
        have h5 : Units.map i.symm.toRingHom.toMonoidHom (Units.map i.toRingHom.toMonoidHom t) = t :=
          Units.ext (i.symm_apply_apply _)
        rw [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, h5,
          GlobalTheory.LocalFieldIso.absPow_map i hi.cont] at h4
        exact h4
    exact gdOf K Ω A w h' rc' hrc' a σ' hplain
  have br : ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O), Induces Bw →
      ∃ (Bw' : LocBridge l K Ω (Dec (F := K) A) O) (_ : Induces Bw'), Bw'.Kw = Bw.Kw ∧ Bw'.j = Bw.j ∧ Bw'.LL = Bw.LL :=
    fun O _ _ _ Bw hj => by
      obtain ⟨Bw', e1, e2, e3⟩ := UpperTheory.V.Af.Cq.exBridge F K Ω l A O Bw (GlobalTheory.T.local_field_embedding_mem F Ω K l A O Bw hdec)
      exact ⟨Bw', fun x => by rw [e2]; exact hj x, e1, e2, e3⟩
  refine ⟨fun B hB => ST.1.2 ((plainOf K a ha P w).2 (ST.2 ⟨B, hB⟩)), fun σ hσ hp rc hrc => ?_, fun σ hσ hp O _ _ _ Bw hj => ?_,
    fun hl hp => ?_, fun O _ _ _ Bw hj σ hσ hs => ?_⟩
  · obtain ⟨e, he⟩ := hBC.split v w i hi.cont hi.loc σ σ' hσ hσ'
    have hy := recTr L.aut.art hi σ σ' e he hrc hrc' hp
    have g := up σ hσ hp
    refine ⟨fun hl => ?_, fun O _ _ _ Bw hj _ => ?_⟩
    · obtain ⟨x, hx, hxx⟩ := _root_.GlobalTheory.ParamSplitPlace.main F Ω K l ι a r A v w h h' i hi _
        (isWDOf_wdOf (h := h') (hlw hl) ι (Units.continuous_val.comp hG.cont))
      exact ⟨x, hx, fun _ => inj hxx hy ((hG.away w (hlw hl) A h' rc' hrc' σ' hσ').tor g.1 g.2)⟩
    · obtain ⟨Bw', hj', e1, e2, e3⟩ := br O Bw hj
      obtain ⟨-, a2, -, a4⟩ := (hG.above _ _ (Loc.tiedP l) w A h' O Bw' hj').nice σ' hσ' rc' hrc' (Or.inr g.1) g.2
      have hpst := (GlobalTheory.T.local_embedding_compatible_extension F Ω K l _ A O Bw Bw' e1 e2 e3 a r).2.2.2.1 a2
      exact ⟨hpst, inj (GlobalTheory.T.local_embedding_restrict_extension F Ω K l _ A O Bw Bw' e1 e2 e3 a r hpst ι v w h h' hj hj' i hi) hy (a4.tor g.1 g.2)⟩
  · have g := up σ hσ hp
    obtain ⟨Bw', hj', e1, e2, e3⟩ := br O Bw hj
    obtain ⟨a1, -, a3, -⟩ := (hG.above _ _ (Loc.tiedP l) w A h' O Bw' hj').nice σ' hσ' rc' hrc' (Or.inr g.1) g.2
    have D := GlobalTheory.T.local_embedding_compatible_extension F Ω K l (Loc.PP l) A O Bw Bw' e1 e2 e3 a r
    refine ⟨D.1 a1, fun τ LL' τ' hτ => ?_⟩
    obtain ⟨τK, τ'', hτK, hind⟩ := GlobalTheory.T.local_embedding_agree F Ω K l A O Bw Bw' e1 e2 τ LL' τ' hτ
    have hJ := D.2.2.2.2 τK (HT τK) (a3 τK LL' τ'' hind)
    rw [hHT τK, hτK] at hJ
    exact hJ
  · have hp' := ST.1.1 hp
    have g := gdOf K Ω A w h' rc' hrc' a σ' (hp' σ' hσ')
    obtain ⟨t, ht⟩ := winPt UpperTheory.V.Z.Gam.suppFacts UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winOf K a ha P
    obtain ⟨x, hx, hxx⟩ := _root_.GlobalTheory.ParamSplitPlace.main F Ω K l ι a r A v w h h' i hi _
      (isWDOf_wdOf (h := h') (hlw hl) ι (Units.continuous_val.comp hG.cont))
    rw [hx.wdOf_eq hl]
    refine UpperTheory.GalN.V.RatioW.descend hi hxx ?_
    rw [(hG.away w (hlw hl) A h' rc' hrc' σ' hσ').tor g.1 g.2]
    exact ratioT K Ω A w h' rc' hrc' a P t (ht w hp') σ' hσ'
  · obtain ⟨e, he⟩ := hBC.split v w i hi.cont hi.loc σ σ' hσ hσ'
    obtain ⟨Bw', hj', e1, e2, e3⟩ := br O Bw hj
    exact (GlobalTheory.T.local_embedding_compatible_extension F Ω K l _ A O Bw Bw' e1 e2 e3 a r).2.2.1
      ((hG.above _ _ (Loc.tiedP l) w A h' O Bw' hj').crys σ' hσ' ((_root_.GlobalTheory.CompletionIso.iwahori_spherical_transfer F K v w i hi.cont a σ σ' e he).2 hs)).1
end Descent
theorem galois_rep_exists_totally_real_rank_two_of_base_change : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → UpperTheory.V.Z.Bc.QuadBC2 → AdmissibleReal → GaloisRepExistsTotallyRealGL2 := by
  intro litN qbc adm F Ω _ _ _ _ _ _ l _ ι a ha2 ha π χ hreg hpol
  let S : Set (QCM F Ω) := {Q | ∃ P : CuspSub ↥Q.K a, IsBC π P}
  have good : ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v →
      {Q : QCM F Ω | Dec (F := F) A ≤ (res F Ω ↥Q.K).range ∧ ∃ P : CuspSub ↥Q.K a, IsBC π P}.Infinite := by
    intro v A hA
    obtain rfl := ha2.out
    have hT := _root_.GlobalTheory.RealGal.SatAeProof.main adm F 2 π
    refine (GlobalTheory.T.infinite_quadratic_fields_split_inertia F Ω (fun u => ∃ B, π.HasSat u B) hT v A hA).mono ?_
    rintro Q ⟨hdec, u, A', ⟨B, hB⟩, hA', hine⟩
    refine ⟨hdec, ?_⟩
    rcases qbc F Q.K Q.two π hreg with ⟨η, hq, htw⟩ | hP
    · exact absurd (_root_.GlobalTheory.T.inertia_le_range_of_unramified_alt litN F Ω Q.K Q.two η hq u A' hA' (unrAt_of_isoTwist adm F 2 ha π η htw u B hB)) hine
    · exact hP
  obtain ⟨v0⟩ : Nonempty (HeightOneSpectrum (𝓞 F)) := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
    exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField F)⟩⟩
  obtain ⟨A0, hA0⟩ := ReciprocityTheory.Gal.exists_isPlaceOver (F := F) Ω v0
  have hS : S.Infinite := by
    refine (good v0 A0 hA0).mono ?_
    intro Q hQ
    exact hQ.2
  have key : ∀ Q : ↥S, ∃ (P : CuspSub ↥Q.1.K a)
      (r : G ↥Q.1.K Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (↥Q.1.K →+* Qbar l) → Multiset ℤ),
      IsBC π P ∧ UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) P ι r wt HT := by
    rintro ⟨Q, P, hP⟩
    obtain ⟨hregP, χ', hχ'⟩ := _root_.GlobalTheory.T.regular_algebraic_and_polarized_of_quadratic_base_change litN F ↥Q.K Q.two a ha π χ P hreg hpol hP
    obtain ⟨r, wt, HT, hr⟩ := _root_.UpperTheory.Gal.SV.rowOf' litN.aut.gal ↥Q.K Ω l ι a ha P χ' hregP hχ'
    exact ⟨P, r, wt, HT, hP, hr⟩
  choose P r wt HT hP hr using key
  have hatt : ∀ Q, Continuous (r Q) ∧ IsSSRep (r Q) ∧ AttRes π ι ↥Q.1.K (r Q) := fun Q =>
    ⟨(hr Q).cont, (hr Q).ss,
      _root_.UpperTheory.Gal.SV.attRes_alt litN F Ω ↥Q.1.K l ι a ha π (P Q) (hP Q) (r Q) (wt Q) (HT Q) (hr Q)⟩
  obtain ⟨ρ, hρc, hρs, hev⟩ := _root_.GlobalTheory.CMPatch.main F Ω l ι a π S hS r hatt
  obtain ⟨HTF, hcard, hwts, hbc⟩ := hodgeTate F Ω l ι a π hreg
  have hgal : ∀ᶠ Q : ↥S in Filter.cofinite,
      UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) (P Q) ι (ρ.comp (res F Ω ↥Q.1.K)) (wt Q) (HT Q) :=
    hev.mono fun Q hQ => props_iso (hr Q) hQ.1 hQ.2
  have hHT : ∀ Q : ↥S, (∀ τ : ↥Q.1.K →+* Qbar l, HT Q τ = HTF (τ.comp (algebraMap F ↥Q.1.K))) ∧
      ∀ τ : F →+* Qbar l, HTF τ = (HTF τ).map (wt Q - ·) :=
    fun Q => hbc ↥Q.1.K Q.1.two (P Q) (hP Q) (r Q) (wt Q) (HT Q) (hr Q)
  obtain ⟨Q0⟩ : Nonempty ↥S := hS.nonempty.to_subtype
  let τ0 : F →+* Qbar l := ι.symm.toRingHom.comp (Classical.arbitrary (InfinitePlace F)).embedding
  have hwt : ∀ Q : ↥S, wt Q = wt Q0 := fun Q =>
    _root_.GlobalTheory.Glob.symm_multiset_centre_unique (HTF τ0) (wt Q) (wt Q0) (by rw [← Multiset.card_pos, hcard]; exact ha) ((hHT Q).2 τ0) ((hHT Q0).2 τ0)
  have hpick : ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v →
      ∃ Q : ↥S, Dec (F := F) A ≤ (res F Ω ↥Q.1.K).range ∧
        UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) (P Q) ι (ρ.comp (res F Ω ↥Q.1.K)) (wt Q) (HT Q) := by
    intro v A hA
    have hfin := (Filter.eventually_cofinite.1 hgal).image Subtype.val
    obtain ⟨Q, hQ, hQn⟩ := ((good v A hA).sdiff hfin).nonempty
    refine ⟨⟨Q, hQ.2⟩, hQ.1, ?_⟩
    by_contra hc
    exact hQn ⟨⟨Q, hQ.2⟩, hc, rfl⟩
  have hD : ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A v), At π ι ρ HTF h := fun v A h => by
    obtain ⟨Q, hdec, hQ⟩ := hpick v A h
    exact _root_.UpperTheory.Gal.SV.local_condition_at_place_of_decomposition_le_range litN ha (hP Q) hQ h hdec (hHT Q).1
  have hpl : ∀ w B, π.HasSat w B → PlainAtR π w := fun w B hB => by
    obtain ⟨A, h⟩ := ReciprocityTheory.Gal.exists_isPlaceOver (F := F) Ω w
    exact (hD w A h).plain B hB
  refine ⟨ρ, wt Q0, HTF, hρc, hρs, hpl, fun w σ hσ hp => ⟨fun A h => (hD w A h).cmp σ hσ hp, fun A h => (hD w A h).ht σ hσ hp⟩,
    fun w hw B hB => ?_, fun w hw A h => (hD w A h).ratio hw, hwts, (hHT Q0).2, fun w A h => (hD w A h).crys⟩
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := _root_.GlobalTheory.RealGal.locCompR_of_admissibleReal adm F a π w
  have hS := ((_root_.GlobalTheory.RealGal.SatLocProof.main F a w σ).2 _ π.finPart (hiso σ hσ) B).1 hB
  exact frob_of hw σ hS fun A h rc hrc => (((hD w A h).cmp σ hσ (hpl w B hB σ hσ) rc hrc).1 hw).isWDOf
    (gdOf F Ω A w h rc hrc a σ (hpl w B hB σ hσ))
end UpperTheory.Gal.SV
end
end
end

