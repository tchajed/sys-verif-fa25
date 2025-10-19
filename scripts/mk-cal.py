#!/usr/bin/env -S uv run


import datetime
import io
from typing import final
import argparse


def md_link(text: str, url: str) -> str:
    return f"[{text}]({url})"


def notes_link(title: str, text: str = "notes"):
    return f"{md_link(text, f'./notes/{title}.md')}"


@final
class TableRow:
    def __init__(
        self,
        num: int | None,
        date: datetime.date,
        lecture: str,
        reading: str,
        comment: str,
    ):
        self.num = num
        self.date = date
        self.lecture = lecture
        self.reading = reading
        self.comment = comment

    def render(self):
        # date format like Thu Sep 4
        num = f"{self.num:2}" if self.num else "  "
        return f"| {num} | {self.date.strftime('%a %b %d')} | {self.lecture} | {self.reading} | {self.comment} |"


@final
class Lecture:
    def __init__(self, title: str, notes: str, has_slides: bool, comment: str):
        self.title = title
        self.notes = notes
        self.has_slides = has_slides
        self.comment = comment

    def row(self, num: int, date: datetime.date) -> TableRow:
        lecture = self.title
        if self.has_slides:
            slides_url = f"./slides/lec{num}.pdf"
            lecture = f"{self.title}: {md_link('slides', slides_url)}"
        return TableRow(num, date, lecture, self.notes, self.comment)


@final
class NoClass:
    def __init__(self, reason: str):
        self.reason = reason

    def row(self, date: datetime.date) -> TableRow:
        return TableRow(
            None, date, f"**No class** ({self.reason})", reading="", comment=""
        )


@final
class AssignmentDue:
    def __init__(self, title: str, url: str, date: datetime.date):
        self.title = title
        self.url = url
        self.date = date

    def row(self):
        link = md_link(f"{self.title}", self.url)
        return TableRow(
            None, self.date, lecture="", reading="", comment=f"_{link} due (11pm)_"
        )


def next_date(date: datetime.date, weekdays: list[int]):
    date += datetime.timedelta(days=1)
    while date.weekday() not in weekdays:
        date += datetime.timedelta(days=1)
    return date


def to_calendar(
    entries: list[Lecture | NoClass | AssignmentDue], start_date: datetime.date
) -> str:
    buffer = io.StringIO()
    date = start_date
    # decide if tue/thu or mon/wed based on first day
    weekdays = [1, 3] if start_date.weekday() in [1, 3] else [0, 2]
    lec_num = 1

    print("<!-- markdownlint-disable MD041 -->", file=buffer)
    print("| | Date | Lecture | Reading | |", file=buffer)
    print("| --- | --- | --- | --- | --- |", file=buffer)
    for e in entries:
        row: TableRow | None = None
        if isinstance(e, Lecture):
            row = e.row(lec_num, date)
            date = next_date(date, weekdays)
            lec_num += 1
        if isinstance(e, NoClass):
            row = e.row(date)
            date = next_date(date, weekdays)
        if isinstance(e, AssignmentDue):
            row = e.row()
        if row:
            print(row.render(), file=buffer)
    return buffer.getvalue()


entries: list[Lecture | AssignmentDue | NoClass] = [
    Lecture("Introduction", notes_link("overview"), has_slides=True, comment=""),
    Lecture(
        "Rocq introduction",
        f"{notes_link('rocq_intro')}, {md_link('tool setup', './assignments/setup.md')}, {md_link('syllabus', './syllabus.md')}",
        has_slides=True,
        comment="bring a laptop",
    ),
    Lecture("Induction", notes_link("induction"), has_slides=True, comment=""),
    Lecture("Abstraction", notes_link("adt_specs"), has_slides=True, comment=""),
    Lecture(
        "Hoare logic (part 1)",
        notes_link("hoare"),
        has_slides=True,
        comment="theory lecture",
    ),
    Lecture(
        "Hoare logic (part 2)",
        notes_link("hoare", text="same notes"),
        has_slides=True,
        comment="theory lecture",
    ),
    Lecture(
        "Separation logic (part 1)",
        notes_link("sep-logic"),
        has_slides=True,
        comment="theory lecture",
    ),
    AssignmentDue("Assignment 1", "./assignments/hw1/", datetime.date(2025, 9, 29)),
    Lecture(
        "Separation logic (part 2)",
        notes_link("sep-logic", text="same notes"),
        has_slides=True,
        comment="theory lecture",
    ),
    NoClass("Tej is traveling"),
    Lecture(
        "Iris Proof Mode (part 1)",
        notes_link("ipm"),
        has_slides=False,
        comment="bring a laptop",
    ),
    NoClass("Tej is sick"),
    Lecture(
        "Iris Proof Mode (part 2)",
        notes_link("ipm", text="same notes"),
        has_slides=False,
        comment="bring a laptop",
    ),
    Lecture("Modeling Go programs", notes_link("goose"), has_slides=True, comment=""),
    AssignmentDue("Assignment 2", "./assignments/hw2/", datetime.date(2025, 10, 20)),
    Lecture(
        "Loop invariants", notes_link("loop_invariants"), has_slides=False, comment=""
    ),
    Lecture("Ownership", notes_link("ownership"), has_slides=False, comment=""),
    Lecture("Persistence", notes_link("persistently"), has_slides=False, comment=""),
    Lecture(
        "Concurrency intro", notes_link("concurrency"), has_slides=False, comment=""
    ),
    Lecture("Lock invariants", notes_link("invariants"), has_slides=False, comment=""),
    Lecture(
        "Resource algebras",
        notes_link("resource-algebra"),
        has_slides=False,
        comment="",
    ),
    AssignmentDue("Assignment 3", "./assignments/hw3/", datetime.date(2025, 11, 10)),
    Lecture("Ghost state", notes_link("ghost_state"), has_slides=False, comment=""),
    Lecture("Atomic specs", notes_link("atomic_specs"), has_slides=False, comment=""),
    Lecture(
        "Barrier proof (spec)", notes_link("barrier"), has_slides=False, comment=""
    ),
    Lecture("Barrier proof", notes_link(""), has_slides=False, comment=""),
    Lecture("Property-based testing", notes_link("pbt"), has_slides=False, comment=""),
    NoClass("Thanksgiving"),
    Lecture("Liveness", notes_link("liveness"), has_slides=False, comment=""),
    Lecture("_slack_", "", has_slides=False, comment=""),
    Lecture("Course wrap-up", notes_link("summary"), has_slides=False, comment=""),
    AssignmentDue("Assignment 4", "./assignments/hw4/", datetime.date(2025, 12, 11)),
]

# Had a week off for SOSP in Fall 2024.
# Fall 2025 has fewer lecture days.
# Fall 2025 had one travel day for NESVD and one sick day.
# Dropped SMT lecture


def main():
    parser = argparse.ArgumentParser()
    _ = parser.add_argument("output", type=argparse.FileType("w"))
    args = parser.parse_args()
    print(
        to_calendar(entries, start_date=datetime.date(2025, 9, 4)),
        end="",
        file=args.output,
    )


if __name__ == "__main__":
    main()
