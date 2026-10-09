// The Surprise Exam Paradox.
//
// A teacher says: "There will be a surprise exam one day next week. You will
// not know which day until it happens."
//
// The students reason: it cannot be Friday, since after Thursday passes, we
// would know. Then Thursday is the last possible day, so it cannot be
// Thursday either. Same for Wednesday, Tuesday, and Monday: there is no exam!
//
// The exam comes on Wednesday. Everyone is surprised.
//
// The key is what "surprise" means. This file defines it, and shows that the
// teacher and the students are using it in two different ways. Both are
// proven correct by Dafny.

// The days of the week: 1 (Monday) to 5 (Friday).
ghost function Week(): set<nat>
{
    {1, 2, 3, 4, 5}
}

// `C` is the set of days the students think the exam could be on.
//
// On the evening before day `d`, the exam has not happened yet, so the
// students know it is on day `d` or on a later day in `C`. An exam on day `d`
// is a surprise if they cannot be sure it is day `d`: some later day in `C`
// is still possible.
ghost predicate Surprise(C: set<nat>, d: nat)
{
    exists x :: x in C && x > d
}

// The days of the week on which an exam would be a surprise, when the
// possible days are `C`.
ghost function SurpriseDays(C: set<nat>): set<nat>
{
    set d | d in Week() && Surprise(C, d)
}

// ---------------------------------------------------------------------------
// The teacher's reading: any day of the week is possible.
// ---------------------------------------------------------------------------

// An exam on Wednesday is a surprise: Thursday and Friday are still possible.
lemma WednesdayIsSurprise()
    ensures Surprise(Week(), 3)
{
    assert 4 in Week();
}

// An exam on Friday is not a surprise: no later day is left.
lemma FridayIsNotSurprise()
    ensures !Surprise(Week(), 5)
{

}

// Every day except Friday is a surprise, so the teacher can keep the promise.
lemma TeacherSurpriseDays()
    ensures SurpriseDays(Week()) == {1, 2, 3, 4}
{
    assert Surprise(Week(), 1) && Surprise(Week(), 2) && Surprise(Week(), 3) && Surprise(Week(), 4) by {
        assert 5 in Week();
    }
}

// ---------------------------------------------------------------------------
// The students' reading: the exam is a surprise, and they know it. So the
// possible days are exactly the days on which an exam would be a surprise,
// when the possible days are those same days:
//
//     C == SurpriseDays(C)
//
// The possible days are defined in terms of themselves.
// ---------------------------------------------------------------------------

// The students' backward reasoning: no possible day is after day `j`.
// Start from Friday (j = 5), then Thursday (j = 4), and so on.
lemma NoneAfter(C: set<nat>, j: nat)
    requires C == SurpriseDays(C)
    requires j <= 5
    ensures forall x | x in C :: x <= j
    decreases 5 - j
{
    if j < 5 {
        // Induction: no possible day is after day j + 1.
        NoneAfter(C, j + 1);
        // If day j + 1 were possible, an exam on it would have to be a
        // surprise, but no later day is possible.
        assert j + 1 !in C;
    }
}

// So no day is possible: "there is no exam!"
lemma StudentsConclusion(C: set<nat>)
    requires C == SurpriseDays(C)
    ensures C == {}
{
    NoneAfter(C, 0);
}

// ---------------------------------------------------------------------------
// Where the two readings disagree
// ---------------------------------------------------------------------------

// The teacher's set of possible days is not one the students accept: an exam
// on Friday would not be a surprise, so Friday drops out.
lemma TeacherAndStudentsDisagree()
    ensures SurpriseDays(Week()) != Week()
{
    TeacherSurpriseDays();
}

// Both readings are proven. The students' reasoning is correct, but it
// answers a different question: it treats "the exam is a surprise" as known
// for sure, and that statement cannot stay true once the students know it.
// The teacher only promised that the exam would be a surprise, with every day
// of the week possible. In that reading, Wednesday is a surprise.
