module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyExhaustion.PropsExh
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0193
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.PrinSeriesWord
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOrderedFormSnoc
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.ExhGood

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ind₂_map_injective_right {r t N : ℕ} (e : Fin r ⊕ Fin t ≃ Fin N) {U W W' : Type} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (σ : Representation ℂ (GL (Fin r) k) U)
    {ρ : Representation ℂ (GL (Fin t) k) W} {ρ' : Representation ℂ (GL (Fin t) k) W'} (f : ρ.IntertwiningMap ρ')
    (hf : Function.Injective f) :
    ∃ F : (ind₂ e (extTensor σ ρ)).IntertwiningMap (ind₂ e (extTensor σ ρ')), Function.Injective F := by
  have hι : Function.Injective (GlobalTheory.ParIndExact.extTensorMapRight σ f) :=
    Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap hf
  have hι' : Function.Injective
      (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ f) (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) := hι
  exact ⟨parIndMap (two e)
      (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ f) (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom),
    GlobalTheory.ParIndExact.parIndMap_injective _ _ hι'⟩

theorem pair_equiv {N : ℕ} (y : Fin 2 → IrrGL (k := k)) (hd : ∑ i, (y i).1 = N) {a : IrrGL (k := k)} (ha : y 0 = a)
    (h : a.1 + (y 1).1 = N) :
    Nonempty ((ind₂ (stdSum h) (extTensor a.rep (y 1).rep)).Equiv (prodIrr y hd)) := by
  subst ha h
  exact nonempty_prod₂_equiv_prodIrr_rep y hd

theorem embed_family {N c : ℕ} (y : Fin 2 → IrrGL (k := k)) (v : Fin (c + 1) → IrrGL (k := k)) (t : Fin c → IrrGL (k := k))
    (h0 : y 0 = v 0) (hs : ∀ i, v i.succ = t i) (hd : ∑ i, (y i).1 = N) (hv : ∑ i, (v i).1 = N)
    (ht : ∑ i, (t i).1 = (y 1).1) (g : (y 1).rep.IntertwiningMap (prodIrr t ht)) (hg : Function.Injective g) :
    ∃ F : (prodIrr y hd).IntertwiningMap (prodIrr v hv), Function.Injective F := by
  have e : t = fun i => v i.succ := funext fun i => (hs i).symm
  subst e
  have h : (v 0).1 + (y 1).1 = N := by
    rw [← h0, ← hd, Fin.sum_univ_two]
  have A0 := pair_equiv y hd h0 h
  have B0 := GlobalTheory.ProdReorder.multiProd_head (k := k) (d := fun i => (v i).1) (fun i => (v i).rep)
    (stdBlocks (fun i => (v i).1) hv) h (stdBlocks (fun i : Fin c => (v i.succ).1) ht)
  have F0 := ind₂_map_injective_right (stdSum h) (v 0).rep g hg
  obtain ⟨A⟩ := A0
  obtain ⟨B⟩ := B0
  obtain ⟨F, hF⟩ := F0
  exact ⟨(B.symm.toIntertwiningMap.comp F).comp A.symm.toIntertwiningMap,
    B.symm.toLinearEquiv.injective.comp (hF.comp A.symm.toLinearEquiv.injective)⟩

theorem isOrderedForm_snoc {h : ℕ} {Δ : Fin h → Segment k} {𝔫 : Multiset (Segment k)} (H : IsOrderedForm Δ 𝔫)
    (s : Segment k) (hs : ∀ D ∈ 𝔫, ¬ D.Precedes s) :
    IsOrderedForm (Fin.snoc (α := fun _ => Segment k) Δ s) (𝔫 + {s}) := by
  refine ⟨?_, fun i j hij => ?_⟩
  · rw [← H.1, Fin.univ_val_map, Fin.univ_val_map, List.ofFn_succ']
    simpa using (Multiset.coe_add _ [s]).symm
  · induction j using Fin.lastCases with
    | last =>
      obtain ⟨i, rfl⟩ : ∃ i', Fin.castSucc i' = i :=
        ⟨i.castPred (Fin.ne_last_of_lt hij), by simp⟩
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact hs _ (H.1 ▸ Multiset.mem_map_of_mem _ (Finset.mem_univ_val i))
    | cast j =>
      obtain ⟨i, rfl⟩ : ∃ i', Fin.castSucc i' = i :=
        ⟨i.castPred (Fin.ne_last_of_lt hij), by simp⟩
      simp only [Fin.snoc_castSucc]
      exact H.2 i j (by simpa using hij)

end GlobalTheory.CompanionTheory.ExhGood

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSubquotientExtTensorRight
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.ProdSubquot
open TensorProduct

section General
variable {G H V V' W W' : Type} [Group G] [Group H]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

theorem isSubquotient_extTensor_left {σ : Representation ℂ G V} {σ' : Representation ℂ G V'}
    (B : Representation ℂ H W) (h : IsSubquotient σ σ') :
    IsSubquotient (extTensor σ B) (extTensor σ' B) := by
  obtain ⟨S, f, hf⟩ := h
  let ι : S.toRepresentation.IntertwiningMap σ' :=
    { toLinearMap := S.toSubmodule.subtype, isIntertwining' := fun _ => rfl }
  have hι : Function.Injective ι := Subtype.val_injective
  obtain ⟨ι', hι'⟩ := GlobalTheory.ParIndExact.extTensor_injective_left B ι hι
  have hs : Function.Surjective (GlobalTheory.ParIndExact.extTensorMapLeft B f) :=
    LinearMap.rTensor_surjective W hf
  exact (IsSubquotient.of_surjective _ hs).trans (IsSubquotient.of_injective ι' hι')

theorem isSubquotient_extTensor_right {ρ : Representation ℂ H W} {ρ' : Representation ℂ H W'}
    (A : Representation ℂ G V) (h : IsSubquotient ρ ρ') :
    IsSubquotient (extTensor A ρ) (extTensor A ρ') := by
  obtain ⟨S, f, hf⟩ := h
  let ι : S.toRepresentation.IntertwiningMap ρ' :=
    { toLinearMap := S.toSubmodule.subtype, isIntertwining' := fun _ => rfl }
  have hι : Function.Injective ι := Subtype.val_injective
  obtain ⟨ι', hι'⟩ := GlobalTheory.ParIndExact.extTensor_injective_right A ι hι
  have hs : Function.Surjective (GlobalTheory.ParIndExact.extTensorMapRight A f) :=
    LinearMap.lTensor_surjective V hf
  exact (IsSubquotient.of_surjective _ hs).trans (IsSubquotient.of_injective ι' hι')

theorem isSubquotient_comp {L : Type} [Group L] {σ : Representation ℂ G V}
    {σ' : Representation ℂ G V'} (s : L →* G) (h : IsSubquotient σ σ') :
    IsSubquotient (σ.comp s) (σ'.comp s) := by
  obtain ⟨S, f, hf⟩ := h
  let T : Subrepresentation (σ'.comp s) :=
    ⟨S.toSubmodule, fun x _ hv => S.apply_mem_toSubmodule (s x) hv⟩
  exact ⟨T, ⟨f.toLinearMap, fun x => f.isIntertwining' (s x)⟩, hf⟩

end General

theorem prod₂_isSubquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (U U' W W' : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (σ : Representation ℂ (GL (Fin r) k) U) (σ' : Representation ℂ (GL (Fin r) k) U') (ρ : Representation ℂ (GL (Fin t) k) W) (ρ' : Representation ℂ (GL (Fin t) k) W'), IsSmooth σ' → IsSmooth ρ' → IsSubquotient σ σ' → IsSubquotient ρ ρ' → IsSubquotient (prod₂ σ ρ) (prod₂ σ' ρ') := by
  intro k _ _ _ _ r t U U' W W' _ _ _ _ _ _ _ _ σ σ' ρ ρ' hσ' hρ' hs hr
  have hext : IsSubquotient (extTensor σ ρ) (extTensor σ' ρ') :=
    (isSubquotient_extTensor_left ρ hs).trans (isSubquotient_extTensor_right σ' hr)
  have hsm : IsSmooth ((extTensor σ' ρ').comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) :=
    isSmooth_comp (isSmooth_extTensor hσ' hρ') _
      (show Continuous fun g : Levi k (Two (Fin r) (Fin t)) => (g false, g true) from
        (continuous_apply false).prodMk (continuous_apply true))
  exact GlobalTheory.ParIndSubquot.parInd_isSubquotient k _ _ _ _ _ _ _ _ hsm
    (isSubquotient_comp _ hext)

end GlobalTheory.CompanionTheory.ProdSubquot
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriAndMaximalCompactCriteria
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.IwEntries

variable {E : Type} [Field E] [NumberField E]

theorem rel_le_one_iff (w : Pl E) (x : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) x ≤ 1 ↔ Valued.v x ≤ 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).le_one_iff_le_one

theorem rel_lt_one_iff (w : Pl E) (x : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) x < 1 ↔ Valued.v x < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).lt_one_iff_lt_one

theorem mem_KGL_iff (w : Pl E) (n : ℕ) (g : GLw n w) :
    g ∈ GlobalTheory.LFun.KGL w (n := n) ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1 := by
  have key : ∀ x : GLw n w, x ∈ GlobalTheory.LFun.KGL w (n := n) → ∀ i j, Valued.v (x.val i j) ≤ 1 := by
    rintro x ⟨u, rfl⟩ i j
    exact (u.val i j).2
  constructor
  · exact fun h => ⟨key g h, key _ (inv_mem h)⟩
  · rintro ⟨h1, h2⟩
    have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) (Ov E w) => A.map (Ov E w).subtype :=
      Matrix.map_injective Subtype.val_injective
    refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨(g⁻¹ : GLw n w).1 i j, h2 i j⟩,
      hi ?_, hi ?_⟩, Units.ext rfl⟩
    · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.mul_inv
    · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.inv_mul

theorem mem_KO_iff (w : Pl E) (n : ℕ) (g : GLw n w) :
    g ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) ↔
      (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1 := by
  have key : ∀ x : GLw n w, x ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) →
      ∀ i j, Valued.v (x.val i j) ≤ 1 := by
    rintro x ⟨u, rfl⟩ i j
    exact (rel_le_one_iff w _).1 (u.val i j).2
  constructor
  · exact fun h => ⟨key g h, key _ (inv_mem h)⟩
  · rintro ⟨h1, h2⟩
    let O := ValuativeRel.valuation (w.adicCompletion E) |>.integer
    have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
      Matrix.map_injective Subtype.val_injective
    refine ⟨⟨Matrix.of fun i j => ⟨_, (rel_le_one_iff w _).2 (h1 i j)⟩,
      Matrix.of fun i j => ⟨(g⁻¹ : GLw n w).1 i j, (rel_le_one_iff w _).2 (h2 i j)⟩, hi ?_, hi ?_⟩,
      Units.ext rfl⟩
    · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.mul_inv
    · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.inv_mul

theorem iwGL_KGL_entries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ) (g : GLw n w), (g ∈ iwGL n w ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ (∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1) ∧ ∀ i j, j < i → Valued.v (g.val i j) < 1) ∧ (g ∈ GlobalTheory.LFun.KGL w (n := n) ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1) := by
  intro E _ _ _ w n g
  refine ⟨?_, mem_KGL_iff w n g⟩
  show g ∈ GlobalTheory.SmGL.iwahori (w.adicCompletion E) (Fin n) ↔ _
  rw [GlobalTheory.SmGL.mem_iwahori, mem_KO_iff, and_assoc]
  exact and_congr_right' (and_congr_right' (forall₃_congr fun i j _ => rel_lt_one_iff w _))

end GlobalTheory.CompanionTheory.IwEntries
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.FrobJm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem piTensor_rep_isIrreducible (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h : ℕ} (x : Fin h → IrrGL (k := k)) :
    (piTensor fun a => (x a).rep).IsIrreducible := by
  have hKex : ∀ N : ℕ, ∃ K : Subgroup (GL (Fin N) k),
      IsOpen (K : Set (GL (Fin N) k)) ∧ IsCompact (K : Set (GL (Fin N) k)) := by
    intro N
    have hT2 : T2Space k := inferInstance
    let O : Subring k := (ValuativeRel.valuation k).integer
    have hOo : IsOpen (O : Set k) := (ValuativeRel.valuation k).isOpen_integer
    have hOc : IsCompact (O : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall (K := k) 1
    let K : Subgroup (GL (Fin N) k) :=
      { carrier := {g | (∀ i j, (g : Matrix (Fin N) (Fin N) k) i j ∈ O) ∧
            ∀ i j, ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j ∈ O}
        mul_mem' := by
          rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
          refine ⟨fun i j => ?_, fun i j => ?_⟩
          · rw [Units.val_mul, Matrix.mul_apply]
            exact sum_mem fun l _ => mul_mem (ha1 i l) (hb1 l j)
          · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
            exact sum_mem fun l _ => mul_mem (hb2 i l) (ha2 l j)
        one_mem' := by
          refine ⟨fun i j => ?_, fun i j => ?_⟩
          · rw [Units.val_one, Matrix.one_apply]
            split_ifs
            exacts [one_mem _, zero_mem _]
          · rw [inv_one, Units.val_one, Matrix.one_apply]
            split_ifs
            exacts [one_mem _, zero_mem _]
        inv_mem' := by
          rintro a ⟨ha1, ha2⟩
          exact ⟨ha2, by rw [inv_inv]; exact ha1⟩ }
    have hKset : (K : Set (GL (Fin N) k)) =
        (⋂ i, ⋂ j, (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i j) ⁻¹' (O : Set k)) ∩
          ⋂ i, ⋂ j, (fun g : GL (Fin N) k => ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j) ⁻¹' (O : Set k) := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
      exact Iff.rfl
    refine ⟨K, ?_, ?_⟩
    · rw [hKset]
      refine IsOpen.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hOo.preimage ?_)
        (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hOo.preimage ?_)
      · exact Units.continuous_val.matrix_elem i j
      · exact Units.continuous_coe_inv.matrix_elem i j
    · rw [Units.isEmbedding_embedProduct.isInducing.isCompact_iff]
      let S : Set (Matrix (Fin N) (Fin N) k) := {A | ∀ i j, A i j ∈ O}
      have hS : IsCompact S := by
        have h := isCompact_univ_pi (fun _ : Fin N => isCompact_univ_pi (fun _ : Fin N => hOc))
        have hSe : S = Set.univ.pi (fun _ : Fin N => Set.univ.pi fun _ : Fin N => (O : Set k)) := by
          ext A
          show (∀ i j, A i j ∈ O) ↔ ∀ i ∈ (Set.univ : Set (Fin N)), ∀ j ∈ (Set.univ : Set (Fin N)), A i j ∈ (O : Set k)
          constructor
          · intro hA i _ j _
            exact hA i j
          · intro hA i j
            exact hA i (Set.mem_univ i) j (Set.mem_univ j)
        rw [hSe]
        exact h
      have hsub : Units.embedProduct (Matrix (Fin N) (Fin N) k) '' (K : Set (GL (Fin N) k)) =
          (S ×ˢ (MulOpposite.op '' S)) ∩
            {p | p.1 * MulOpposite.unop p.2 = 1 ∧ MulOpposite.unop p.2 * p.1 = 1} := by
        ext p
        constructor
        · rintro ⟨g, ⟨hg1, hg2⟩, rfl⟩
          exact ⟨⟨hg1, (g⁻¹ : GL (Fin N) k).val, hg2, rfl⟩, g.mul_inv, g.inv_mul⟩
        · rintro ⟨⟨hA, B, hB, hBp⟩, h1, h2⟩
          refine ⟨⟨p.1, MulOpposite.unop p.2, h1, h2⟩, ⟨hA, ?_⟩, rfl⟩
          show ∀ i j, (MulOpposite.unop p.2) i j ∈ O
          rw [← hBp]
          exact hB
      rw [hsub]
      refine (hS.prod (hS.image MulOpposite.continuous_op)).inter_right ?_
      exact (isClosed_eq (continuous_fst.mul (MulOpposite.continuous_unop.comp continuous_snd))
        continuous_const).inter
        (isClosed_eq ((MulOpposite.continuous_unop.comp continuous_snd).mul continuous_fst) continuous_const)
  refine GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (x a).2.rep.irr) ?_
  intro a φ hφ
  obtain ⟨K, hKo, hKc⟩ := hKex (x a).1
  exact GlobalTheory.SchurAdm.schur_admissible _ K hKo hKc _ _ (x a).2.rep.irr
    (hA k _ _ _ (x a).2.rep.smooth (x a).2.rep.irr) φ hφ

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem eval_map (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : τ.IntertwiningMap (parInd e ρ)) (g : GL n k) (v : V) :
    (f (τ g v)).1.1 1 = (f v).1.1 g := by
  have hf : f (τ g v) = parInd e ρ g (f v) := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun (f.isIntertwining' g) v
  rw [hf, parInd_apply, one_mul]

theorem eval_unipRad (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) W} (φ : IndSp e ρ)
    (u : unipRad k e) : φ.1.1 (u : GL n k) = φ.1.1 1 := by
  have hp : (u : GL n k) ∈ parab k e := unipRad_le_parab k e u.2
  have hl : leviProj k e ⟨u, hp⟩ = 1 := (coe_mem_unipRad k (e := e) ⟨(u : GL n k), hp⟩).1 u.2
  have hφ := parInd_law e ρ φ ⟨u, hp⟩ 1
  rw [hl] at hφ
  simpa using hφ

def evalOne (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : τ.IntertwiningMap (parInd e ρ)) : V →ₗ[ℂ] W where
  toFun v := (f v).1.1 1
  map_add' v w := by simp
  map_smul' c v := by simp

theorem twKer_le_ker_evalOne (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V}
    {ρ : Representation ℂ (Levi k m) W} (f : τ.IntertwiningMap (parInd e ρ)) :
    twKer τ (unipRad k e) 1 ≤ LinearMap.ker (evalOne e f) := by
  unfold GlobalTheory.PRep.twKer
  rw [Submodule.span_le]
  rintro w ⟨u, v, rfl⟩
  have hu : evalOne e f (τ (u : GL n k) v) = evalOne e f v := by
    show (f (τ (u : GL n k) v)).1.1 1 = (f v).1.1 1
    rw [eval_map, eval_unipRad e (f v) u]
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hu, MonoidHom.one_apply,
    Units.val_one, one_smul, sub_self]

def frobMap (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : τ.IntertwiningMap (parInd e ρ)) : (GlobalTheory.SmGL.jac e τ).IntertwiningMap ρ where
  toLinearMap := (twKer τ (unipRad k e) 1).liftQ (evalOne e f) (twKer_le_ker_evalOne e f)
  isIntertwining' g := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hmem : leviEmb k e g ∈ parab k e := by
      refine mem_parab_iff.2 fun a b i j hab => ?_
      simp [leviEmb, Matrix.blockDiagonal'_apply, hab.ne']
    have hproj : leviProj k e ⟨leviEmb k e g, hmem⟩ = g := by
      funext a
      ext i j
      simp [leviEmb]
    have h := parInd_law e ρ (f v) ⟨leviEmb k e g, hmem⟩ 1
    rw [mul_one, hproj] at h
    have h2 : evalOne e f (τ (leviEmb k e g) v) =
        (deltaHalf k m g : ℂ) • ρ g (evalOne e f v) := (eval_map e f _ v).trans h
    show (twKer τ (unipRad k e) 1).liftQ (evalOne e f) (twKer_le_ker_evalOne e f)
        (GlobalTheory.SmGL.jac e τ g (Submodule.Quotient.mk v)) = ρ g (evalOne e f v)
    rw [jac_mk, map_smul]
    change (((deltaHalf k m g)⁻¹ : ℂˣ) : ℂ) • evalOne e f (τ (leviEmb k e g) v) = _
    rw [h2, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

theorem frobMap_mk (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : τ.IntertwiningMap (parInd e ρ)) (v : V) :
    frobMap e f (Submodule.Quotient.mk v) = (f v).1.1 1 := rfl

theorem frobMap_ne_zero (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : τ.IntertwiningMap (parInd e ρ)) (hf : ∃ v, f v ≠ 0) : ∃ y, frobMap e f y ≠ 0 := by
  obtain ⟨v, hv⟩ := hf
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  apply hv
  apply Subtype.ext
  apply Subtype.ext
  funext g
  have h1 := frobMap_mk e f (τ g v)
  rw [hcon, eval_map] at h1
  simpa using h1.symm

theorem surjective_of_ne_zero {G : Type} [Group G] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (hσ : σ.IsIrreducible) (f : ρ.IntertwiningMap σ) (hf : ∃ y, f y ≠ 0) : Function.Surjective f := by
  haveI := hσ
  rcases Representation.IsIrreducible.surjective_or_eq_zero f with hs | hz
  · exact hs
  · obtain ⟨y, hy⟩ := hf
    exact (hy (by simp [hz])).elim

theorem one_le_jm : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V : Type}
    [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GL (Fin N) k) V), IsSmooth τ →
    ∀ f : τ.IntertwiningMap (prodIrr x hd), (∃ v, f v ≠ 0) → 1 ≤ jm x hd τ := by
  intro k _ _ _ _ hA h N x hd V _ _ τ _ f hf
  let f' : τ.IntertwiningMap (parInd (stdBlocks (fun a => (x a).1) hd) (piTensor fun a => (x a).rep)) := f
  obtain ⟨y, hy⟩ := frobMap_ne_zero _ f' hf
  have hs := surjective_of_ne_zero (piTensor_rep_isIrreducible hA x) (frobMap _ f') ⟨y, hy⟩
  have hq := jhMult_ne_zero_iff.2 (IsSubquotient.of_surjective _ hs)
  exact Order.one_le_iff_ne_zero.2 hq

end GlobalTheory.CompanionTheory.FrobJm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeQuotientTorsionNonzero
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

theorem exists_ne_zero_smul_mem_of_mem_span {K : Type} [Field K] [NumberField K] {m : ℕ}
    (L : Submodule (𝓞 K) (Fin m → K)) {v : Fin m → K}
    (hv : v ∈ Submodule.span K (L : Set (Fin m → K))) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ L := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have e : (a * b) • (x + y) = b • (a • x) + a • (b • y) := by
      rw [smul_add, mul_smul, mul_comm, mul_smul]
      rw [smul_comm a b x, smul_comm b a y]
    rw [e]
    exact L.add_mem (L.smul_mem _ hax) (L.smul_mem _ hby)
  | smul k x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) k
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hdK : algebraMap (𝓞 K) K d ≠ 0 := by
      simpa using hd0
    refine ⟨d * a, mul_ne_zero hd0 ha, ?_⟩
    have e : (d * a) • ((algebraMap (𝓞 K) K n / algebraMap (𝓞 K) K d) • x) = n • (a • x) := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      simp only [Algebra.smul_def, map_mul]
      field_simp
    rw [e]
    exact L.smul_mem _ hax

theorem torsionOf_quot_lat_ne_bot : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ)
    (L : Submodule (𝓞 K) (Fin m → K)), IsLat L →
    ∀ x : (Fin m → K) ⧸ L, Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x ≠ ⊥ := by
  intro K _ _ m L hL x h
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective L x
  obtain ⟨a, ha, hav⟩ := exists_ne_zero_smul_mem_of_mem_span L
    (show v ∈ Submodule.span K (L : Set (Fin m → K)) by rw [hL.2]; trivial)
  have hmem : a ∈ Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) (Submodule.Quotient.mk v) := by
    rw [Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul]
    exact (Submodule.Quotient.mk_eq_zero L).2 hav
  rw [h] at hmem
  exact ha ((Submodule.mem_bot _).1 hmem)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
end
end

