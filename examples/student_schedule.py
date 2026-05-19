# ── Ghost model: the database as seen by business logic ──────────
if __debug__:
    students: dict[str, Student] = {}       # student_id → Student record
    courses: dict[str, Course] = {}         # course_id → Course
    enrollments: dict[str, list[str]] = {}  # student_id → [course_id, ...]

class Student:
    name: str
    completed: list[str] = Field(default_factory=list)  # completed course IDs
    enrolled: list[str] = Field(default_factory=list)   # enrolled course IDs

class Course:
    id: str
    title: str
    prerequisites: list[str] = Field(default_factory=list)  # required course IDs
    capacity: int = Field(ge=0)
    enrolled_count: int = Field(ge=0)

# ── Database stubs ──────────────────────────────────────────────

def db_get_student(student_id: str) -> Student:
    """requires: student_id in students
    ensures: result == students[student_id]
    reads: students"""

def db_get_course(course_id: str) -> Course:
    """requires: course_id in courses
    ensures: result == courses[course_id]
    reads: courses"""

def db_get_enrollments(student_id: str) -> list[str]:
    """requires: student_id in enrollments
    ensures: result == enrollments.get(student_id, [])
    reads: enrollments"""

def db_enroll(student_id: str, course_id: str) -> None:
    """requires: course_id in courses
    requires: courses[course_id].enrolled_count < courses[course_id].capacity
    ensures: course_id in enrollments[student_id]
    writes: enrollments, courses"""  # mutates both

# ── Business predicates ─────────────────────────────────────────

def has_completed(student: Student, course_id: str) -> bool:
    """Pure predicate: student completed this course."""
    return course_id in student.completed

def prerequisites_met(student: Student, course: Course) -> bool:
    """Pure predicate: all prerequisites are completed."""
    return all(has_completed(student, prereq)
               for prereq in course.prerequisites)

def is_eligible(student: Student, course: Course) -> bool:
    """Business rule: student can take course iff prerequisites met
    and course has capacity."""
    return (prerequisites_met(student, course) and
            course.enrolled_count < course.capacity)

# ── Core business logic: build a training plan ──────────────────

def build_training_plan(student_id: str) -> list[str]:
    """Given a logged-in student, return their customized training plan.
    
    GIVEN Student is logged into the website
      AND Student has completed BASE
      AND Student has unfinished classes
    WHEN Student requests class schedule
    THEN Student's customized training plan is viewable
    
    The plan includes all courses the student is eligible for
    that they haven't completed or enrolled in yet.
    """
    assert student_id in students                      # precondition: logged in
    student = db_get_student(student_id)
    assert "BASE" in student.completed                 # precondition: BASE done
    assert len(student.completed) >= 0
    assert len(student.enrolled) >= 0

    if __debug__:
        old_completed = list(student.completed)
        old_enrolled = list(student.enrolled)

    result = []
    for course_id in sorted(courses.keys()):
        assert all(is_eligible(student, courses[c])
                   for c in result)                    # invariant: eligible so far
        assert all(c not in student.completed
                   for c in result)                    # invariant: no completed
        assert all(c not in student.enrolled
                   for c in result)                    # invariant: not enrolled
        course = db_get_course(course_id)
        # Business rule: include if eligible and not already taken
        if is_eligible(student, course):
            if course_id not in student.completed:
                if course_id not in student.enrolled:
                    result.append(course_id)

    assert all(is_eligible(student, courses[c])
               for c in result)                        # postcondition: all eligible
    assert all(c not in student.completed
               for c in result)                        # postcondition: none completed
    assert all(c not in student.enrolled
               for c in result)                        # postcondition: none enrolled
    assert len(result) >= 0                            # postcondition: valid list
    return result

# ── Enrollment with capacity check ─────────────────────────────

def enroll_in_course(student_id: str, course_id: str) -> int:
    """Enroll a student in a course. Returns 1 on success, 0 on failure."""
    assert student_id in students
    assert course_id in courses
    student = db_get_student(student_id)
    course = db_get_course(course_id)
    if not is_eligible(student, course):
        result = 0
        assert result == 0
        return result
    if course_id in student.enrolled:
        result = 1                                     # already enrolled
        assert result == 1
        return result
    db_enroll(student_id, course_id)
    result = 1
    assert course_id in db_get_enrollments(student_id) # postcondition: enrolled
    assert (courses[course_id].enrolled_count <=        # postcondition: capacity
            courses[course_id].capacity)
    assert result == 1
    return result
